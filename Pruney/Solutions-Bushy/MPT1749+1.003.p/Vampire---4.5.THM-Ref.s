%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1749+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 475 expanded)
%              Number of leaves         :    8 (  83 expanded)
%              Depth                    :   29
%              Number of atoms          :  588 (5660 expanded)
%              Number of equality atoms :   79 ( 379 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f725,plain,(
    $false ),
    inference(subsumption_resolution,[],[f694,f114])).

fof(f114,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4) ),
    inference(subsumption_resolution,[],[f113,f38])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ( r2_hidden(X5,u1_struct_0(X2))
                               => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) ) )
                         => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).

fof(f113,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4) ),
    inference(subsumption_resolution,[],[f87,f36])).

fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4) ),
    inference(resolution,[],[f37,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f37,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f694,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4) ),
    inference(backward_demodulation,[],[f39,f693])).

fof(f693,plain,(
    sK4 = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(subsumption_resolution,[],[f692,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f692,plain,
    ( sK4 = k2_tmap_1(sK1,sK0,sK3,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f691,f74])).

fof(f74,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f50,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f691,plain,
    ( sK4 = k2_tmap_1(sK1,sK0,sK3,sK2)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f690,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f690,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK4 = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(subsumption_resolution,[],[f689,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f689,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK4 = k2_tmap_1(sK1,sK0,sK3,sK2)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f688,f73])).

fof(f73,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f47,f68])).

fof(f47,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f688,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK4 = k2_tmap_1(sK1,sK0,sK3,sK2)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f661,f66])).

fof(f661,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK4 = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(subsumption_resolution,[],[f660,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f660,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK4 = k2_tmap_1(sK1,sK0,sK3,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f659,f79])).

fof(f79,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f77,f68])).

fof(f77,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f75,f47])).

fof(f75,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f44,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f44,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f659,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK4 = k2_tmap_1(sK1,sK0,sK3,sK2)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f616,f66])).

fof(f616,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK4 = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(subsumption_resolution,[],[f615,f350])).

fof(f350,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK4 = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(forward_demodulation,[],[f349,f189])).

fof(f189,plain,(
    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f130,f44])).

fof(f130,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f129,f42])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f129,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f128,f45])).

fof(f128,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f127,f40])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f127,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f126,f50])).

fof(f126,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK3)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f125,f49])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f125,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK3)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f124,f48])).

fof(f124,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK3)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f123,f47])).

fof(f123,plain,(
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
    inference(subsumption_resolution,[],[f115,f46])).

fof(f46,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f115,plain,(
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
    inference(resolution,[],[f41,f56])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f41,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f349,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f348,f38])).

fof(f348,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f347,f36])).

fof(f347,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f340,f78])).

fof(f78,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f76,f47])).

fof(f76,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f44,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f340,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f148,f37])).

fof(f148,plain,(
    ! [X8,X9] :
      ( ~ v1_funct_2(X9,X8,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_funct_1(X9)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X8,X9)) != k1_funct_1(X9,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X8,X9))
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X8) = X9 ) ),
    inference(subsumption_resolution,[],[f147,f42])).

fof(f147,plain,(
    ! [X8,X9] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_xboole_0(X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X8,X9)) != k1_funct_1(X9,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X8,X9))
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X8) = X9 ) ),
    inference(subsumption_resolution,[],[f121,f40])).

fof(f121,plain,(
    ! [X8,X9] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_xboole_0(X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X8,X9)) != k1_funct_1(X9,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X8,X9))
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X8) = X9 ) ),
    inference(resolution,[],[f41,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k3_funct_2(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK5(X0,X1,X2,X3,X4))
      | k2_partfun1(X0,X1,X2,X3) = X4 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => ( r2_hidden(X5,X3)
                             => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                       => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_2)).

fof(f615,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK4 = k2_tmap_1(sK1,sK0,sK3,sK2)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) ),
    inference(subsumption_resolution,[],[f613,f220])).

fof(f220,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK4 = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(forward_demodulation,[],[f219,f189])).

fof(f219,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f218,f38])).

fof(f218,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f217,f36])).

fof(f217,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f214,f78])).

fof(f214,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f144,f37])).

fof(f144,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_2(X5,X4,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_funct_1(X5)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,u1_struct_0(sK0))))
      | m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X4,X5),u1_struct_0(sK1))
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X4) = X5 ) ),
    inference(subsumption_resolution,[],[f143,f42])).

fof(f143,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,u1_struct_0(sK0))))
      | m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X4,X5),u1_struct_0(sK1))
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X4) = X5 ) ),
    inference(subsumption_resolution,[],[f119,f40])).

fof(f119,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,u1_struct_0(sK0))))
      | m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X4,X5),u1_struct_0(sK1))
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X4) = X5 ) ),
    inference(resolution,[],[f41,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)
      | k2_partfun1(X0,X1,X2,X3) = X4 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f613,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK4 = k2_tmap_1(sK1,sK0,sK3,sK2)
    | ~ m1_subset_1(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) ),
    inference(resolution,[],[f203,f35])).

fof(f35,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,u1_struct_0(sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | k1_funct_1(sK4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f203,plain,
    ( r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK4 = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(forward_demodulation,[],[f202,f189])).

fof(f202,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f201,f38])).

fof(f201,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f200,f36])).

fof(f200,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f197,f78])).

fof(f197,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4),u1_struct_0(sK2))
    | sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f146,f37])).

fof(f146,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_2(X7,X6,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK1))
      | v1_xboole_0(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_funct_1(X7)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(sK0))))
      | r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X6,X7),X6)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X6) = X7 ) ),
    inference(subsumption_resolution,[],[f145,f42])).

fof(f145,plain,(
    ! [X6,X7] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_xboole_0(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(sK0))))
      | r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X6,X7),X6)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X6) = X7 ) ),
    inference(subsumption_resolution,[],[f120,f40])).

fof(f120,plain,(
    ! [X6,X7] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_xboole_0(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(sK0))))
      | r2_hidden(sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X6,X7),X6)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X6) = X7 ) ),
    inference(resolution,[],[f41,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | r2_hidden(sK5(X0,X1,X2,X3,X4),X3)
      | k2_partfun1(X0,X1,X2,X3) = X4 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
