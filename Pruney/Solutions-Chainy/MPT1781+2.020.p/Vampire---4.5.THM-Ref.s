%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:20 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  217 (5303 expanded)
%              Number of leaves         :   14 ( 915 expanded)
%              Depth                    :   33
%              Number of atoms          : 1420 (45590 expanded)
%              Number of equality atoms :   63 (3101 expanded)
%              Maximal formula depth    :   26 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1519,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1518,f1517])).

fof(f1517,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f1500,f1515])).

fof(f1515,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f1502,f1512])).

fof(f1512,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f1509,f1504])).

fof(f1504,plain,(
    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f1498,f101])).

fof(f101,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f100,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,u1_struct_0(X1))
                       => k1_funct_1(X2,X3) = X3 ) )
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,u1_struct_0(X1))
                     => k1_funct_1(X2,X3) = X3 ) )
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).

fof(f100,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f99,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f99,plain,(
    ! [X1] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f83,f53])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f50,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f50,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f1498,plain,(
    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1433,f48])).

fof(f48,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f1433,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f1086,f1408])).

fof(f1408,plain,(
    k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1407,f1045])).

fof(f1045,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f403,f50])).

fof(f403,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f402,f51])).

fof(f402,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f401,f52])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f401,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f399,f53])).

fof(f399,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f258,f50])).

fof(f258,plain,(
    ! [X14,X15] :
      ( ~ m1_pre_topc(sK1,X14)
      | ~ l1_pre_topc(X14)
      | ~ v2_pre_topc(X14)
      | ~ m1_pre_topc(X15,X14)
      | v2_struct_0(X14)
      | m1_subset_1(k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f257,f94])).

fof(f94,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f93,f51])).

fof(f93,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f92,f53])).

fof(f92,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f81,f52])).

fof(f81,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f50,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(f257,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | v2_struct_0(X14)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f256,f88])).

fof(f88,plain,(
    v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f87,f51])).

fof(f87,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f86,f53])).

fof(f86,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f79,f52])).

fof(f79,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f50,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_1(k4_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f256,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X14)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f255,f53])).

fof(f255,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X14)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f254,f52])).

fof(f254,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X14)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f214,f51])).

fof(f214,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X14)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f91,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f91,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f90,f51])).

fof(f90,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f89,f53])).

fof(f89,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f80,f52])).

fof(f80,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f50,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1407,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f712,f714])).

fof(f714,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f386,f50])).

fof(f386,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f385,f51])).

fof(f385,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f384,f52])).

fof(f384,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f382,f53])).

fof(f382,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f253,f50])).

fof(f253,plain,(
    ! [X12,X13] :
      ( ~ m1_pre_topc(sK1,X12)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | v2_struct_0(X12)
      | v1_funct_2(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(X13),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f252,f94])).

fof(f252,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(sK1,X12)
      | ~ m1_pre_topc(X13,X12)
      | v2_struct_0(X12)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_2(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(X13),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f251,f88])).

fof(f251,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(sK1,X12)
      | ~ m1_pre_topc(X13,X12)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X12)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_2(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(X13),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f250,f53])).

fof(f250,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X12)
      | ~ m1_pre_topc(X13,X12)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X12)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_2(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(X13),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f249,f52])).

fof(f249,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X12)
      | ~ m1_pre_topc(X13,X12)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X12)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_2(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(X13),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f213,f51])).

fof(f213,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X12)
      | ~ m1_pre_topc(X13,X12)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X12)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_2(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(X13),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f91,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f712,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f711,f88])).

fof(f711,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f710,f373])).

fof(f373,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f346,f50])).

fof(f346,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f345,f51])).

fof(f345,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f344,f52])).

fof(f344,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f342,f53])).

fof(f342,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) ) ),
    inference(resolution,[],[f248,f50])).

fof(f248,plain,(
    ! [X10,X11] :
      ( ~ m1_pre_topc(sK1,X10)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | v2_struct_0(X10)
      | v1_funct_1(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f247,f94])).

fof(f247,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(sK1,X10)
      | ~ m1_pre_topc(X11,X10)
      | v2_struct_0(X10)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f246,f88])).

fof(f246,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(sK1,X10)
      | ~ m1_pre_topc(X11,X10)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X10)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f245,f53])).

fof(f245,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X10)
      | ~ m1_pre_topc(X11,X10)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X10)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f244,f52])).

fof(f244,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X10)
      | ~ m1_pre_topc(X11,X10)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X10)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f212,f51])).

fof(f212,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X10)
      | ~ m1_pre_topc(X11,X10)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X10)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1))) ) ),
    inference(resolution,[],[f91,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f710,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f709,f94])).

fof(f709,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f708,f91])).

fof(f708,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f379,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f379,plain,(
    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f378,f51])).

fof(f378,plain,
    ( v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f377,f52])).

fof(f377,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f375,f53])).

fof(f375,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f222,f50])).

fof(f222,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f221,f94])).

fof(f221,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f220,f88])).

fof(f220,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f219,f49])).

fof(f219,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f218,f53])).

fof(f218,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f217,f52])).

fof(f217,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f208,f51])).

fof(f208,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(resolution,[],[f91,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_funct_1(X3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
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
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

fof(f1086,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1085,f52])).

fof(f1085,plain,
    ( ~ v2_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ),
    inference(subsumption_resolution,[],[f1084,f51])).

fof(f1084,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ),
    inference(subsumption_resolution,[],[f1082,f53])).

fof(f1082,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ),
    inference(resolution,[],[f445,f50])).

fof(f445,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ) ),
    inference(subsumption_resolution,[],[f444,f47])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f444,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ) ),
    inference(subsumption_resolution,[],[f443,f45])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f443,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_1(sK2)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ) ),
    inference(subsumption_resolution,[],[f442,f106])).

fof(f106,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f104,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f104,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f85,f53])).

fof(f85,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f50,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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

fof(f442,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK1,sK1)
      | ~ v1_funct_1(sK2)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ) ),
    inference(subsumption_resolution,[],[f439,f49])).

fof(f439,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK1,sK1)
      | ~ v1_funct_1(sK2)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ) ),
    inference(resolution,[],[f229,f46])).

fof(f46,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f229,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK1,X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(X3)
      | ~ v2_pre_topc(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,X2,sK1,k4_tmap_1(sK0,sK1),X3),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k3_tmap_1(X1,sK0,sK1,X2,k4_tmap_1(sK0,sK1)),X3) ) ),
    inference(subsumption_resolution,[],[f228,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f228,plain,(
    ! [X2,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(sK1,X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,X2,sK1,k4_tmap_1(sK0,sK1),X3),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k3_tmap_1(X1,sK0,sK1,X2,k4_tmap_1(sK0,sK1)),X3) ) ),
    inference(subsumption_resolution,[],[f227,f94])).

fof(f227,plain,(
    ! [X2,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(sK1,X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,X2,sK1,k4_tmap_1(sK0,sK1),X3),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k3_tmap_1(X1,sK0,sK1,X2,k4_tmap_1(sK0,sK1)),X3) ) ),
    inference(subsumption_resolution,[],[f226,f88])).

fof(f226,plain,(
    ! [X2,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(sK1,X1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,X2,sK1,k4_tmap_1(sK0,sK1),X3),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k3_tmap_1(X1,sK0,sK1,X2,k4_tmap_1(sK0,sK1)),X3) ) ),
    inference(subsumption_resolution,[],[f225,f49])).

fof(f225,plain,(
    ! [X2,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,X2,sK1,k4_tmap_1(sK0,sK1),X3),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k3_tmap_1(X1,sK0,sK1,X2,k4_tmap_1(sK0,sK1)),X3) ) ),
    inference(subsumption_resolution,[],[f224,f53])).

fof(f224,plain,(
    ! [X2,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,X2,sK1,k4_tmap_1(sK0,sK1),X3),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k3_tmap_1(X1,sK0,sK1,X2,k4_tmap_1(sK0,sK1)),X3) ) ),
    inference(subsumption_resolution,[],[f223,f52])).

fof(f223,plain,(
    ! [X2,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,X2,sK1,k4_tmap_1(sK0,sK1),X3),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k3_tmap_1(X1,sK0,sK1,X2,k4_tmap_1(sK0,sK1)),X3) ) ),
    inference(subsumption_resolution,[],[f209,f51])).

fof(f209,plain,(
    ! [X2,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,X2,sK1,k4_tmap_1(sK0,sK1),X3),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k3_tmap_1(X1,sK0,sK1,X2,k4_tmap_1(sK0,sK1)),X3) ) ),
    inference(resolution,[],[f91,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | m1_subset_1(sK3(X1,X2,X3,X4,X5),u1_struct_0(X3))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          | ? [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) != k1_funct_1(X5,X6)
                              & r2_hidden(X6,u1_struct_0(X2))
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          | ? [X6] :
                              ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) != k1_funct_1(X5,X6)
                              & r2_hidden(X6,u1_struct_0(X2))
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ( r2_hidden(X6,u1_struct_0(X2))
                                   => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                             => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tmap_1)).

fof(f1509,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))
    | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f1499,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f97,f51])).

fof(f97,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f96,f49])).

fof(f96,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f95,f53])).

fof(f95,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f82,f52])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(resolution,[],[f50,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,u1_struct_0(X1))
               => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).

fof(f1499,plain,(
    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1434,f48])).

fof(f1434,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f1094,f1408])).

fof(f1094,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1093,f52])).

fof(f1093,plain,
    ( ~ v2_pre_topc(sK0)
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ),
    inference(subsumption_resolution,[],[f1092,f51])).

fof(f1092,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ),
    inference(subsumption_resolution,[],[f1090,f53])).

fof(f1090,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ),
    inference(resolution,[],[f461,f50])).

fof(f461,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ) ),
    inference(subsumption_resolution,[],[f460,f47])).

fof(f460,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ) ),
    inference(subsumption_resolution,[],[f459,f45])).

fof(f459,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_1(sK2)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ) ),
    inference(subsumption_resolution,[],[f458,f106])).

fof(f458,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK1,sK1)
      | ~ v1_funct_1(sK2)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ) ),
    inference(subsumption_resolution,[],[f455,f49])).

fof(f455,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK1,sK1)
      | ~ v1_funct_1(sK2)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ) ),
    inference(resolution,[],[f236,f46])).

fof(f236,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0))
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(sK1,X4)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X5,sK1)
      | ~ v1_funct_1(X6)
      | ~ v2_pre_topc(X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,X5,sK1,k4_tmap_1(sK0,sK1),X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK0),k3_tmap_1(X4,sK0,sK1,X5,k4_tmap_1(sK0,sK1)),X6) ) ),
    inference(subsumption_resolution,[],[f235,f67])).

fof(f235,plain,(
    ! [X6,X4,X5] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(sK1,X4)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X5,sK1)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,X5,sK1,k4_tmap_1(sK0,sK1),X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK0),k3_tmap_1(X4,sK0,sK1,X5,k4_tmap_1(sK0,sK1)),X6) ) ),
    inference(subsumption_resolution,[],[f234,f94])).

fof(f234,plain,(
    ! [X6,X4,X5] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(sK1,X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X5,sK1)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,X5,sK1,k4_tmap_1(sK0,sK1),X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK0),k3_tmap_1(X4,sK0,sK1,X5,k4_tmap_1(sK0,sK1)),X6) ) ),
    inference(subsumption_resolution,[],[f233,f88])).

fof(f233,plain,(
    ! [X6,X4,X5] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(sK1,X4)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X4)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X5,sK1)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,X5,sK1,k4_tmap_1(sK0,sK1),X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK0),k3_tmap_1(X4,sK0,sK1,X5,k4_tmap_1(sK0,sK1)),X6) ) ),
    inference(subsumption_resolution,[],[f232,f49])).

fof(f232,plain,(
    ! [X6,X4,X5] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X4)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X4)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X4)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X5,sK1)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,X5,sK1,k4_tmap_1(sK0,sK1),X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK0),k3_tmap_1(X4,sK0,sK1,X5,k4_tmap_1(sK0,sK1)),X6) ) ),
    inference(subsumption_resolution,[],[f231,f53])).

fof(f231,plain,(
    ! [X6,X4,X5] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X4)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X4)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X4)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X5,sK1)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,X5,sK1,k4_tmap_1(sK0,sK1),X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK0),k3_tmap_1(X4,sK0,sK1,X5,k4_tmap_1(sK0,sK1)),X6) ) ),
    inference(subsumption_resolution,[],[f230,f52])).

fof(f230,plain,(
    ! [X6,X4,X5] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X4)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X4)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X4)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X5,sK1)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,X5,sK1,k4_tmap_1(sK0,sK1),X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK0),k3_tmap_1(X4,sK0,sK1,X5,k4_tmap_1(sK0,sK1)),X6) ) ),
    inference(subsumption_resolution,[],[f210,f51])).

fof(f210,plain,(
    ! [X6,X4,X5] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X4)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X4)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X4)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X5,sK1)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,X5,sK1,k4_tmap_1(sK0,sK1),X6),u1_struct_0(X5))
      | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK0),k3_tmap_1(X4,sK0,sK1,X5,k4_tmap_1(sK0,sK1)),X6) ) ),
    inference(resolution,[],[f91,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | r2_hidden(sK3(X1,X2,X3,X4,X5),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1502,plain,(
    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f1498,f261])).

fof(f261,plain,(
    ! [X16] :
      ( ~ m1_subset_1(X16,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16) ) ),
    inference(subsumption_resolution,[],[f260,f94])).

fof(f260,plain,(
    ! [X16] :
      ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16) ) ),
    inference(subsumption_resolution,[],[f259,f166])).

fof(f166,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f165,f49])).

fof(f165,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f105,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f105,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f104,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f259,plain,(
    ! [X16] :
      ( v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16) ) ),
    inference(subsumption_resolution,[],[f215,f88])).

fof(f215,plain,(
    ! [X16] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16) ) ),
    inference(resolution,[],[f91,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f1500,plain,(
    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f1437,f48])).

fof(f1437,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f1198,f1408])).

fof(f1198,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ),
    inference(subsumption_resolution,[],[f1197,f52])).

fof(f1197,plain,
    ( ~ v2_pre_topc(sK0)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ),
    inference(subsumption_resolution,[],[f1196,f51])).

fof(f1196,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ),
    inference(subsumption_resolution,[],[f1194,f53])).

fof(f1194,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ),
    inference(resolution,[],[f667,f50])).

fof(f667,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ) ),
    inference(subsumption_resolution,[],[f666,f47])).

fof(f666,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ) ),
    inference(subsumption_resolution,[],[f665,f45])).

fof(f665,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_1(sK2)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ) ),
    inference(subsumption_resolution,[],[f664,f106])).

fof(f664,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK1,sK1)
      | ~ v1_funct_1(sK2)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ) ),
    inference(subsumption_resolution,[],[f659,f49])).

fof(f659,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK1,sK1)
      | ~ v1_funct_1(sK2)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) ) ),
    inference(resolution,[],[f243,f46])).

fof(f243,plain,(
    ! [X8,X7,X9] :
      ( ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0))
      | ~ l1_pre_topc(X7)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(sK1,X7)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X8,sK1)
      | ~ v1_funct_1(X9)
      | ~ v2_pre_topc(X7)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) != k1_funct_1(X9,sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9))
      | r2_funct_2(u1_struct_0(X8),u1_struct_0(sK0),k3_tmap_1(X7,sK0,sK1,X8,k4_tmap_1(sK0,sK1)),X9) ) ),
    inference(subsumption_resolution,[],[f242,f67])).

fof(f242,plain,(
    ! [X8,X7,X9] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,X7)
      | ~ m1_pre_topc(sK1,X7)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X8,sK1)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) != k1_funct_1(X9,sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9))
      | r2_funct_2(u1_struct_0(X8),u1_struct_0(sK0),k3_tmap_1(X7,sK0,sK1,X8,k4_tmap_1(sK0,sK1)),X9) ) ),
    inference(subsumption_resolution,[],[f241,f94])).

fof(f241,plain,(
    ! [X8,X7,X9] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,X7)
      | ~ m1_pre_topc(sK1,X7)
      | v2_struct_0(X7)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X8,sK1)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) != k1_funct_1(X9,sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9))
      | r2_funct_2(u1_struct_0(X8),u1_struct_0(sK0),k3_tmap_1(X7,sK0,sK1,X8,k4_tmap_1(sK0,sK1)),X9) ) ),
    inference(subsumption_resolution,[],[f240,f88])).

fof(f240,plain,(
    ! [X8,X7,X9] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,X7)
      | ~ m1_pre_topc(sK1,X7)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X7)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X8,sK1)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) != k1_funct_1(X9,sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9))
      | r2_funct_2(u1_struct_0(X8),u1_struct_0(sK0),k3_tmap_1(X7,sK0,sK1,X8,k4_tmap_1(sK0,sK1)),X9) ) ),
    inference(subsumption_resolution,[],[f239,f49])).

fof(f239,plain,(
    ! [X8,X7,X9] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,X7)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X7)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X7)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X8,sK1)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) != k1_funct_1(X9,sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9))
      | r2_funct_2(u1_struct_0(X8),u1_struct_0(sK0),k3_tmap_1(X7,sK0,sK1,X8,k4_tmap_1(sK0,sK1)),X9) ) ),
    inference(subsumption_resolution,[],[f238,f53])).

fof(f238,plain,(
    ! [X8,X7,X9] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,X7)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X7)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X7)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X8,sK1)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) != k1_funct_1(X9,sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9))
      | r2_funct_2(u1_struct_0(X8),u1_struct_0(sK0),k3_tmap_1(X7,sK0,sK1,X8,k4_tmap_1(sK0,sK1)),X9) ) ),
    inference(subsumption_resolution,[],[f237,f52])).

fof(f237,plain,(
    ! [X8,X7,X9] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,X7)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X7)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X7)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X8,sK1)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) != k1_funct_1(X9,sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9))
      | r2_funct_2(u1_struct_0(X8),u1_struct_0(sK0),k3_tmap_1(X7,sK0,sK1,X8,k4_tmap_1(sK0,sK1)),X9) ) ),
    inference(subsumption_resolution,[],[f211,f51])).

fof(f211,plain,(
    ! [X8,X7,X9] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,X7)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X7)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X7)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X8,sK1)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) != k1_funct_1(X9,sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9))
      | r2_funct_2(u1_struct_0(X8),u1_struct_0(sK0),k3_tmap_1(X7,sK0,sK1,X8,k4_tmap_1(sK0,sK1)),X9) ) ),
    inference(resolution,[],[f91,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
      | v2_struct_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,sK3(X1,X2,X3,X4,X5)) != k1_funct_1(X5,sK3(X1,X2,X3,X4,X5))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1518,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f1510,f1504])).

fof(f1510,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))
    | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f1499,f44])).

fof(f44,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k1_funct_1(sK2,X3) = X3 ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (18340)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (18342)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (18341)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (18350)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (18360)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (18352)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (18339)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.28/0.53  % (18338)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.53  % (18358)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.28/0.53  % (18344)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.28/0.53  % (18359)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.28/0.53  % (18348)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.28/0.53  % (18350)Refutation not found, incomplete strategy% (18350)------------------------------
% 1.28/0.53  % (18350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (18356)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.45/0.54  % (18349)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.45/0.54  % (18347)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.45/0.55  % (18337)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.45/0.55  % (18337)Refutation not found, incomplete strategy% (18337)------------------------------
% 1.45/0.55  % (18337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (18337)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (18337)Memory used [KB]: 10618
% 1.45/0.55  % (18337)Time elapsed: 0.127 s
% 1.45/0.55  % (18337)------------------------------
% 1.45/0.55  % (18337)------------------------------
% 1.45/0.56  % (18350)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (18350)Memory used [KB]: 6268
% 1.45/0.56  % (18350)Time elapsed: 0.119 s
% 1.45/0.56  % (18350)------------------------------
% 1.45/0.56  % (18350)------------------------------
% 1.45/0.56  % (18354)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.45/0.56  % (18351)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.45/0.56  % (18346)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.45/0.56  % (18361)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.45/0.57  % (18353)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.45/0.57  % (18343)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.45/0.58  % (18355)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.45/0.58  % (18345)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.45/0.59  % (18357)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.45/0.60  % (18362)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.45/0.62  % (18348)Refutation not found, incomplete strategy% (18348)------------------------------
% 1.45/0.62  % (18348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.62  % (18348)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.62  
% 1.45/0.62  % (18348)Memory used [KB]: 11001
% 1.45/0.62  % (18348)Time elapsed: 0.202 s
% 1.45/0.62  % (18348)------------------------------
% 1.45/0.62  % (18348)------------------------------
% 1.45/0.64  % (18342)Refutation found. Thanks to Tanya!
% 1.45/0.64  % SZS status Theorem for theBenchmark
% 1.45/0.64  % SZS output start Proof for theBenchmark
% 1.45/0.64  fof(f1519,plain,(
% 1.45/0.64    $false),
% 1.45/0.64    inference(subsumption_resolution,[],[f1518,f1517])).
% 1.45/0.64  fof(f1517,plain,(
% 1.45/0.64    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 1.45/0.64    inference(backward_demodulation,[],[f1500,f1515])).
% 1.45/0.64  fof(f1515,plain,(
% 1.45/0.64    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 1.45/0.64    inference(backward_demodulation,[],[f1502,f1512])).
% 1.45/0.64  fof(f1512,plain,(
% 1.45/0.64    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 1.45/0.64    inference(subsumption_resolution,[],[f1509,f1504])).
% 1.45/0.64  fof(f1504,plain,(
% 1.45/0.64    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))),
% 1.45/0.64    inference(resolution,[],[f1498,f101])).
% 1.45/0.64  fof(f101,plain,(
% 1.45/0.64    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.45/0.64    inference(subsumption_resolution,[],[f100,f51])).
% 1.45/0.64  fof(f51,plain,(
% 1.45/0.64    ~v2_struct_0(sK0)),
% 1.45/0.64    inference(cnf_transformation,[],[f18])).
% 1.45/0.64  fof(f18,plain,(
% 1.45/0.64    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.45/0.64    inference(flattening,[],[f17])).
% 1.45/0.64  fof(f17,plain,(
% 1.45/0.64    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.45/0.64    inference(ennf_transformation,[],[f16])).
% 1.45/0.64  fof(f16,negated_conjecture,(
% 1.45/0.64    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 1.45/0.64    inference(negated_conjecture,[],[f15])).
% 1.45/0.64  fof(f15,conjecture,(
% 1.45/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 1.45/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).
% 1.45/0.64  fof(f100,plain,(
% 1.45/0.64    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.45/0.64    inference(subsumption_resolution,[],[f99,f49])).
% 1.45/0.64  fof(f49,plain,(
% 1.45/0.64    ~v2_struct_0(sK1)),
% 1.45/0.64    inference(cnf_transformation,[],[f18])).
% 1.45/0.64  fof(f99,plain,(
% 1.45/0.64    ( ! [X1] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.45/0.64    inference(subsumption_resolution,[],[f83,f53])).
% 1.45/0.64  fof(f53,plain,(
% 1.45/0.64    l1_pre_topc(sK0)),
% 1.45/0.64    inference(cnf_transformation,[],[f18])).
% 1.45/0.64  fof(f83,plain,(
% 1.45/0.64    ( ! [X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.45/0.64    inference(resolution,[],[f50,f66])).
% 1.45/0.64  fof(f66,plain,(
% 1.45/0.64    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 1.45/0.64    inference(cnf_transformation,[],[f34])).
% 1.45/0.64  fof(f34,plain,(
% 1.45/0.64    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/0.64    inference(flattening,[],[f33])).
% 1.45/0.64  fof(f33,plain,(
% 1.45/0.64    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.45/0.64    inference(ennf_transformation,[],[f7])).
% 1.45/0.64  fof(f7,axiom,(
% 1.45/0.64    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.45/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.45/0.64  fof(f50,plain,(
% 1.45/0.64    m1_pre_topc(sK1,sK0)),
% 1.45/0.64    inference(cnf_transformation,[],[f18])).
% 1.45/0.64  fof(f1498,plain,(
% 1.45/0.64    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 1.45/0.64    inference(subsumption_resolution,[],[f1433,f48])).
% 1.45/0.64  fof(f48,plain,(
% 1.45/0.64    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 1.45/0.64    inference(cnf_transformation,[],[f18])).
% 1.45/0.64  fof(f1433,plain,(
% 1.45/0.64    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 1.45/0.64    inference(backward_demodulation,[],[f1086,f1408])).
% 1.45/0.64  fof(f1408,plain,(
% 1.45/0.64    k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 1.45/0.64    inference(subsumption_resolution,[],[f1407,f1045])).
% 1.45/0.64  fof(f1045,plain,(
% 1.45/0.64    m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.45/0.64    inference(resolution,[],[f403,f50])).
% 1.45/0.64  fof(f403,plain,(
% 1.45/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 1.45/0.64    inference(subsumption_resolution,[],[f402,f51])).
% 1.45/0.64  fof(f402,plain,(
% 1.45/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 1.45/0.64    inference(subsumption_resolution,[],[f401,f52])).
% 1.45/0.64  fof(f52,plain,(
% 1.45/0.64    v2_pre_topc(sK0)),
% 1.45/0.64    inference(cnf_transformation,[],[f18])).
% 1.45/0.64  fof(f401,plain,(
% 1.45/0.64    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 1.45/0.64    inference(subsumption_resolution,[],[f399,f53])).
% 1.45/0.64  fof(f399,plain,(
% 1.45/0.64    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 1.45/0.64    inference(resolution,[],[f258,f50])).
% 1.45/0.64  fof(f258,plain,(
% 1.45/0.64    ( ! [X14,X15] : (~m1_pre_topc(sK1,X14) | ~l1_pre_topc(X14) | ~v2_pre_topc(X14) | ~m1_pre_topc(X15,X14) | v2_struct_0(X14) | m1_subset_1(k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(sK0))))) )),
% 1.45/0.64    inference(subsumption_resolution,[],[f257,f94])).
% 1.45/0.64  fof(f94,plain,(
% 1.45/0.64    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.45/0.64    inference(subsumption_resolution,[],[f93,f51])).
% 1.45/0.64  fof(f93,plain,(
% 1.45/0.64    v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.45/0.64    inference(subsumption_resolution,[],[f92,f53])).
% 1.45/0.64  fof(f92,plain,(
% 1.45/0.64    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.45/0.64    inference(subsumption_resolution,[],[f81,f52])).
% 1.45/0.64  fof(f81,plain,(
% 1.45/0.64    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.45/0.64    inference(resolution,[],[f50,f62])).
% 1.45/0.64  fof(f62,plain,(
% 1.45/0.64    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 1.45/0.64    inference(cnf_transformation,[],[f26])).
% 1.45/0.64  fof(f26,plain,(
% 1.45/0.64    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/0.64    inference(flattening,[],[f25])).
% 1.45/0.64  fof(f25,plain,(
% 1.45/0.64    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.45/0.64    inference(ennf_transformation,[],[f9])).
% 1.45/0.64  fof(f9,axiom,(
% 1.45/0.64    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 1.45/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 1.45/0.64  fof(f257,plain,(
% 1.45/0.64    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(sK0))))) )),
% 1.45/0.64    inference(subsumption_resolution,[],[f256,f88])).
% 1.45/0.64  fof(f88,plain,(
% 1.45/0.64    v1_funct_1(k4_tmap_1(sK0,sK1))),
% 1.45/0.64    inference(subsumption_resolution,[],[f87,f51])).
% 1.45/0.64  fof(f87,plain,(
% 1.45/0.64    v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 1.45/0.64    inference(subsumption_resolution,[],[f86,f53])).
% 1.45/0.64  fof(f86,plain,(
% 1.45/0.64    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 1.45/0.64    inference(subsumption_resolution,[],[f79,f52])).
% 1.45/0.64  fof(f79,plain,(
% 1.45/0.64    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 1.45/0.64    inference(resolution,[],[f50,f60])).
% 1.45/0.64  fof(f60,plain,(
% 1.45/0.64    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_1(k4_tmap_1(X0,X1))) )),
% 1.45/0.64    inference(cnf_transformation,[],[f26])).
% 1.45/0.64  fof(f256,plain,(
% 1.45/0.64    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(sK0))))) )),
% 1.45/0.64    inference(subsumption_resolution,[],[f255,f53])).
% 1.45/0.64  fof(f255,plain,(
% 1.45/0.64    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(sK0))))) )),
% 1.45/0.64    inference(subsumption_resolution,[],[f254,f52])).
% 1.45/0.64  fof(f254,plain,(
% 1.45/0.64    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(sK0))))) )),
% 1.45/0.64    inference(subsumption_resolution,[],[f214,f51])).
% 2.21/0.64  fof(f214,plain,(
% 2.21/0.64    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(sK0))))) )),
% 2.21/0.64    inference(resolution,[],[f91,f72])).
% 2.21/0.64  fof(f72,plain,(
% 2.21/0.64    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))) )),
% 2.21/0.64    inference(cnf_transformation,[],[f40])).
% 2.21/0.64  fof(f40,plain,(
% 2.21/0.64    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.64    inference(flattening,[],[f39])).
% 2.21/0.64  fof(f39,plain,(
% 2.21/0.64    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.64    inference(ennf_transformation,[],[f8])).
% 2.21/0.64  fof(f8,axiom,(
% 2.21/0.64    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 2.21/0.64  fof(f91,plain,(
% 2.21/0.64    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.21/0.64    inference(subsumption_resolution,[],[f90,f51])).
% 2.21/0.64  fof(f90,plain,(
% 2.21/0.64    v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.21/0.64    inference(subsumption_resolution,[],[f89,f53])).
% 2.21/0.64  fof(f89,plain,(
% 2.21/0.64    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.21/0.64    inference(subsumption_resolution,[],[f80,f52])).
% 2.21/0.64  fof(f80,plain,(
% 2.21/0.64    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.21/0.64    inference(resolution,[],[f50,f61])).
% 2.21/0.64  fof(f61,plain,(
% 2.21/0.64    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))) )),
% 2.21/0.64    inference(cnf_transformation,[],[f26])).
% 2.21/0.64  fof(f1407,plain,(
% 2.21/0.64    ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.21/0.64    inference(resolution,[],[f712,f714])).
% 2.21/0.64  fof(f714,plain,(
% 2.21/0.64    v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.21/0.64    inference(resolution,[],[f386,f50])).
% 2.21/0.64  fof(f386,plain,(
% 2.21/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 2.21/0.64    inference(subsumption_resolution,[],[f385,f51])).
% 2.21/0.64  fof(f385,plain,(
% 2.21/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 2.21/0.64    inference(subsumption_resolution,[],[f384,f52])).
% 2.21/0.64  fof(f384,plain,(
% 2.21/0.64    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 2.21/0.64    inference(subsumption_resolution,[],[f382,f53])).
% 2.21/0.64  fof(f382,plain,(
% 2.21/0.64    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 2.21/0.64    inference(resolution,[],[f253,f50])).
% 2.21/0.64  fof(f253,plain,(
% 2.21/0.64    ( ! [X12,X13] : (~m1_pre_topc(sK1,X12) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | ~m1_pre_topc(X13,X12) | v2_struct_0(X12) | v1_funct_2(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(X13),u1_struct_0(sK0))) )),
% 2.21/0.64    inference(subsumption_resolution,[],[f252,f94])).
% 2.21/0.64  fof(f252,plain,(
% 2.21/0.64    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(X13),u1_struct_0(sK0))) )),
% 2.21/0.64    inference(subsumption_resolution,[],[f251,f88])).
% 2.21/0.64  fof(f251,plain,(
% 2.21/0.64    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(X13),u1_struct_0(sK0))) )),
% 2.21/0.64    inference(subsumption_resolution,[],[f250,f53])).
% 2.21/0.64  fof(f250,plain,(
% 2.21/0.64    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(X13),u1_struct_0(sK0))) )),
% 2.21/0.64    inference(subsumption_resolution,[],[f249,f52])).
% 2.21/0.64  fof(f249,plain,(
% 2.21/0.64    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(X13),u1_struct_0(sK0))) )),
% 2.21/0.64    inference(subsumption_resolution,[],[f213,f51])).
% 2.21/0.64  fof(f213,plain,(
% 2.21/0.64    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),u1_struct_0(X13),u1_struct_0(sK0))) )),
% 2.21/0.64    inference(resolution,[],[f91,f71])).
% 2.21/0.64  fof(f71,plain,(
% 2.21/0.64    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))) )),
% 2.21/0.64    inference(cnf_transformation,[],[f40])).
% 2.21/0.64  fof(f712,plain,(
% 2.21/0.64    ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.21/0.64    inference(subsumption_resolution,[],[f711,f88])).
% 2.21/0.64  fof(f711,plain,(
% 2.21/0.64    ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.21/0.64    inference(subsumption_resolution,[],[f710,f373])).
% 2.21/0.64  fof(f373,plain,(
% 2.21/0.64    v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.21/0.64    inference(resolution,[],[f346,f50])).
% 2.21/0.64  fof(f346,plain,(
% 2.21/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.64    inference(subsumption_resolution,[],[f345,f51])).
% 2.21/0.64  fof(f345,plain,(
% 2.21/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.64    inference(subsumption_resolution,[],[f344,f52])).
% 2.21/0.64  fof(f344,plain,(
% 2.21/0.64    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.64    inference(subsumption_resolution,[],[f342,f53])).
% 2.21/0.64  fof(f342,plain,(
% 2.21/0.64    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | v1_funct_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.64    inference(resolution,[],[f248,f50])).
% 2.21/0.64  fof(f248,plain,(
% 2.21/0.64    ( ! [X10,X11] : (~m1_pre_topc(sK1,X10) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | ~m1_pre_topc(X11,X10) | v2_struct_0(X10) | v1_funct_1(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.64    inference(subsumption_resolution,[],[f247,f94])).
% 2.21/0.64  fof(f247,plain,(
% 2.21/0.64    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.64    inference(subsumption_resolution,[],[f246,f88])).
% 2.21/0.64  fof(f246,plain,(
% 2.21/0.64    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.64    inference(subsumption_resolution,[],[f245,f53])).
% 2.21/0.64  fof(f245,plain,(
% 2.21/0.64    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.64    inference(subsumption_resolution,[],[f244,f52])).
% 2.21/0.64  fof(f244,plain,(
% 2.21/0.64    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.64    inference(subsumption_resolution,[],[f212,f51])).
% 2.21/0.64  fof(f212,plain,(
% 2.21/0.64    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.64    inference(resolution,[],[f91,f70])).
% 2.21/0.64  fof(f70,plain,(
% 2.21/0.64    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) )),
% 2.21/0.64    inference(cnf_transformation,[],[f40])).
% 2.21/0.64  fof(f710,plain,(
% 2.21/0.64    ~v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.21/0.64    inference(subsumption_resolution,[],[f709,f94])).
% 2.21/0.64  fof(f709,plain,(
% 2.21/0.64    ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.21/0.64    inference(subsumption_resolution,[],[f708,f91])).
% 2.21/0.64  fof(f708,plain,(
% 2.21/0.64    ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.21/0.64    inference(resolution,[],[f379,f55])).
% 2.21/0.64  fof(f55,plain,(
% 2.21/0.64    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~v1_funct_1(X2)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f20])).
% 2.21/0.65  fof(f20,plain,(
% 2.21/0.65    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.21/0.65    inference(flattening,[],[f19])).
% 2.21/0.65  fof(f19,plain,(
% 2.21/0.65    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.21/0.65    inference(ennf_transformation,[],[f3])).
% 2.21/0.65  fof(f3,axiom,(
% 2.21/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.21/0.65  fof(f379,plain,(
% 2.21/0.65    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.21/0.65    inference(subsumption_resolution,[],[f378,f51])).
% 2.21/0.65  fof(f378,plain,(
% 2.21/0.65    v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.21/0.65    inference(subsumption_resolution,[],[f377,f52])).
% 2.21/0.65  fof(f377,plain,(
% 2.21/0.65    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.21/0.65    inference(subsumption_resolution,[],[f375,f53])).
% 2.21/0.65  fof(f375,plain,(
% 2.21/0.65    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.21/0.65    inference(resolution,[],[f222,f50])).
% 2.21/0.65  fof(f222,plain,(
% 2.21/0.65    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f221,f94])).
% 2.21/0.65  fof(f221,plain,(
% 2.21/0.65    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | v2_struct_0(X0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f220,f88])).
% 2.21/0.65  fof(f220,plain,(
% 2.21/0.65    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f219,f49])).
% 2.21/0.65  fof(f219,plain,(
% 2.21/0.65    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f218,f53])).
% 2.21/0.65  fof(f218,plain,(
% 2.21/0.65    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f217,f52])).
% 2.21/0.65  fof(f217,plain,(
% 2.21/0.65    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f208,f51])).
% 2.21/0.65  fof(f208,plain,(
% 2.21/0.65    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.21/0.65    inference(resolution,[],[f91,f56])).
% 2.21/0.65  fof(f56,plain,(
% 2.21/0.65    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))) )),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  fof(f22,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.65    inference(flattening,[],[f21])).
% 2.21/0.65  fof(f21,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.65    inference(ennf_transformation,[],[f12])).
% 2.21/0.65  fof(f12,axiom,(
% 2.21/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).
% 2.21/0.65  fof(f1086,plain,(
% 2.21/0.65    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.21/0.65    inference(subsumption_resolution,[],[f1085,f52])).
% 2.21/0.65  fof(f1085,plain,(
% 2.21/0.65    ~v2_pre_topc(sK0) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)),
% 2.21/0.65    inference(subsumption_resolution,[],[f1084,f51])).
% 2.21/0.65  fof(f1084,plain,(
% 2.21/0.65    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)),
% 2.21/0.65    inference(subsumption_resolution,[],[f1082,f53])).
% 2.21/0.65  fof(f1082,plain,(
% 2.21/0.65    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)),
% 2.21/0.65    inference(resolution,[],[f445,f50])).
% 2.21/0.65  fof(f445,plain,(
% 2.21/0.65    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f444,f47])).
% 2.21/0.65  fof(f47,plain,(
% 2.21/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.21/0.65    inference(cnf_transformation,[],[f18])).
% 2.21/0.65  fof(f444,plain,(
% 2.21/0.65    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f443,f45])).
% 2.21/0.65  fof(f45,plain,(
% 2.21/0.65    v1_funct_1(sK2)),
% 2.21/0.65    inference(cnf_transformation,[],[f18])).
% 2.21/0.65  fof(f443,plain,(
% 2.21/0.65    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | v2_struct_0(X0) | ~v1_funct_1(sK2) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f442,f106])).
% 2.21/0.65  fof(f106,plain,(
% 2.21/0.65    m1_pre_topc(sK1,sK1)),
% 2.21/0.65    inference(resolution,[],[f104,f69])).
% 2.21/0.65  fof(f69,plain,(
% 2.21/0.65    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f38])).
% 2.21/0.65  fof(f38,plain,(
% 2.21/0.65    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.21/0.65    inference(ennf_transformation,[],[f10])).
% 2.21/0.65  fof(f10,axiom,(
% 2.21/0.65    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.21/0.65  fof(f104,plain,(
% 2.21/0.65    l1_pre_topc(sK1)),
% 2.21/0.65    inference(subsumption_resolution,[],[f85,f53])).
% 2.21/0.65  fof(f85,plain,(
% 2.21/0.65    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 2.21/0.65    inference(resolution,[],[f50,f68])).
% 2.21/0.65  fof(f68,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f37])).
% 2.21/0.65  fof(f37,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.21/0.65    inference(ennf_transformation,[],[f5])).
% 2.21/0.65  fof(f5,axiom,(
% 2.21/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.21/0.65  fof(f442,plain,(
% 2.21/0.65    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | v2_struct_0(X0) | ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f439,f49])).
% 2.21/0.65  fof(f439,plain,(
% 2.21/0.65    ( ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | v2_struct_0(X0) | ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)) )),
% 2.21/0.65    inference(resolution,[],[f229,f46])).
% 2.21/0.65  fof(f46,plain,(
% 2.21/0.65    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.21/0.65    inference(cnf_transformation,[],[f18])).
% 2.21/0.65  fof(f229,plain,(
% 2.21/0.65    ( ! [X2,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(sK1,X1) | v2_struct_0(X1) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v2_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,X2,sK1,k4_tmap_1(sK0,sK1),X3),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k3_tmap_1(X1,sK0,sK1,X2,k4_tmap_1(sK0,sK1)),X3)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f228,f67])).
% 2.21/0.65  fof(f67,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f36])).
% 2.21/0.65  fof(f36,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.21/0.65    inference(flattening,[],[f35])).
% 2.21/0.65  fof(f35,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.21/0.65    inference(ennf_transformation,[],[f13])).
% 2.21/0.65  fof(f13,axiom,(
% 2.21/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 2.21/0.65  fof(f228,plain,(
% 2.21/0.65    ( ! [X2,X3,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(sK1,X1) | v2_struct_0(X1) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,X2,sK1,k4_tmap_1(sK0,sK1),X3),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k3_tmap_1(X1,sK0,sK1,X2,k4_tmap_1(sK0,sK1)),X3)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f227,f94])).
% 2.21/0.65  fof(f227,plain,(
% 2.21/0.65    ( ! [X2,X3,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(sK1,X1) | v2_struct_0(X1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,X2,sK1,k4_tmap_1(sK0,sK1),X3),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k3_tmap_1(X1,sK0,sK1,X2,k4_tmap_1(sK0,sK1)),X3)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f226,f88])).
% 2.21/0.65  fof(f226,plain,(
% 2.21/0.65    ( ! [X2,X3,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(sK1,X1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,X2,sK1,k4_tmap_1(sK0,sK1),X3),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k3_tmap_1(X1,sK0,sK1,X2,k4_tmap_1(sK0,sK1)),X3)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f225,f49])).
% 2.21/0.65  fof(f225,plain,(
% 2.21/0.65    ( ! [X2,X3,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,X2,sK1,k4_tmap_1(sK0,sK1),X3),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k3_tmap_1(X1,sK0,sK1,X2,k4_tmap_1(sK0,sK1)),X3)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f224,f53])).
% 2.21/0.65  fof(f224,plain,(
% 2.21/0.65    ( ! [X2,X3,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,X2,sK1,k4_tmap_1(sK0,sK1),X3),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k3_tmap_1(X1,sK0,sK1,X2,k4_tmap_1(sK0,sK1)),X3)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f223,f52])).
% 2.21/0.65  fof(f223,plain,(
% 2.21/0.65    ( ! [X2,X3,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,X2,sK1,k4_tmap_1(sK0,sK1),X3),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k3_tmap_1(X1,sK0,sK1,X2,k4_tmap_1(sK0,sK1)),X3)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f209,f51])).
% 2.21/0.65  fof(f209,plain,(
% 2.21/0.65    ( ! [X2,X3,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,X2,sK1,k4_tmap_1(sK0,sK1),X3),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k3_tmap_1(X1,sK0,sK1,X2,k4_tmap_1(sK0,sK1)),X3)) )),
% 2.21/0.65    inference(resolution,[],[f91,f57])).
% 2.21/0.65  fof(f57,plain,(
% 2.21/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | m1_subset_1(sK3(X1,X2,X3,X4,X5),u1_struct_0(X3)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f24])).
% 2.21/0.65  fof(f24,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) | ? [X6] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) != k1_funct_1(X5,X6) & r2_hidden(X6,u1_struct_0(X2)) & m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.65    inference(flattening,[],[f23])).
% 2.21/0.65  fof(f23,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) | ? [X6] : ((k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) != k1_funct_1(X5,X6) & r2_hidden(X6,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.65    inference(ennf_transformation,[],[f11])).
% 2.21/0.65  fof(f11,axiom,(
% 2.21/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => (r2_hidden(X6,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tmap_1)).
% 2.21/0.65  fof(f1509,plain,(
% 2.21/0.65    ~m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0)) | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.21/0.65    inference(resolution,[],[f1499,f98])).
% 2.21/0.65  fof(f98,plain,(
% 2.21/0.65    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f97,f51])).
% 2.21/0.65  fof(f97,plain,(
% 2.21/0.65    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f96,f49])).
% 2.21/0.65  fof(f96,plain,(
% 2.21/0.65    ( ! [X0] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f95,f53])).
% 2.21/0.65  fof(f95,plain,(
% 2.21/0.65    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f82,f52])).
% 2.21/0.65  fof(f82,plain,(
% 2.21/0.65    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.21/0.65    inference(resolution,[],[f50,f63])).
% 2.21/0.65  fof(f63,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2) )),
% 2.21/0.65    inference(cnf_transformation,[],[f28])).
% 2.21/0.65  fof(f28,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.65    inference(flattening,[],[f27])).
% 2.21/0.65  fof(f27,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.65    inference(ennf_transformation,[],[f14])).
% 2.21/0.65  fof(f14,axiom,(
% 2.21/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).
% 2.21/0.65  fof(f1499,plain,(
% 2.21/0.65    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.21/0.65    inference(subsumption_resolution,[],[f1434,f48])).
% 2.21/0.65  fof(f1434,plain,(
% 2.21/0.65    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.21/0.65    inference(backward_demodulation,[],[f1094,f1408])).
% 2.21/0.65  fof(f1094,plain,(
% 2.21/0.65    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.21/0.65    inference(subsumption_resolution,[],[f1093,f52])).
% 2.21/0.65  fof(f1093,plain,(
% 2.21/0.65    ~v2_pre_topc(sK0) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)),
% 2.21/0.65    inference(subsumption_resolution,[],[f1092,f51])).
% 2.21/0.65  fof(f1092,plain,(
% 2.21/0.65    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)),
% 2.21/0.65    inference(subsumption_resolution,[],[f1090,f53])).
% 2.21/0.65  fof(f1090,plain,(
% 2.21/0.65    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)),
% 2.21/0.65    inference(resolution,[],[f461,f50])).
% 2.21/0.65  fof(f461,plain,(
% 2.21/0.65    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f460,f47])).
% 2.21/0.65  fof(f460,plain,(
% 2.21/0.65    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f459,f45])).
% 2.21/0.65  fof(f459,plain,(
% 2.21/0.65    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | v2_struct_0(X0) | ~v1_funct_1(sK2) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f458,f106])).
% 2.21/0.65  fof(f458,plain,(
% 2.21/0.65    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | v2_struct_0(X0) | ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f455,f49])).
% 2.21/0.65  fof(f455,plain,(
% 2.21/0.65    ( ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | v2_struct_0(X0) | ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)) )),
% 2.21/0.65    inference(resolution,[],[f236,f46])).
% 2.21/0.65  fof(f236,plain,(
% 2.21/0.65    ( ! [X6,X4,X5] : (~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0)) | ~l1_pre_topc(X4) | v2_struct_0(X5) | ~m1_pre_topc(sK1,X4) | v2_struct_0(X4) | ~m1_pre_topc(X5,sK1) | ~v1_funct_1(X6) | ~v2_pre_topc(X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,X5,sK1,k4_tmap_1(sK0,sK1),X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK0),k3_tmap_1(X4,sK0,sK1,X5,k4_tmap_1(sK0,sK1)),X6)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f235,f67])).
% 2.21/0.65  fof(f235,plain,(
% 2.21/0.65    ( ! [X6,X4,X5] : (~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK1,X4) | v2_struct_0(X4) | ~m1_pre_topc(X5,sK1) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,X5,sK1,k4_tmap_1(sK0,sK1),X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK0),k3_tmap_1(X4,sK0,sK1,X5,k4_tmap_1(sK0,sK1)),X6)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f234,f94])).
% 2.21/0.65  fof(f234,plain,(
% 2.21/0.65    ( ! [X6,X4,X5] : (~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK1,X4) | v2_struct_0(X4) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X5,sK1) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,X5,sK1,k4_tmap_1(sK0,sK1),X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK0),k3_tmap_1(X4,sK0,sK1,X5,k4_tmap_1(sK0,sK1)),X6)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f233,f88])).
% 2.21/0.65  fof(f233,plain,(
% 2.21/0.65    ( ! [X6,X4,X5] : (~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK1,X4) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X4) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X5,sK1) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,X5,sK1,k4_tmap_1(sK0,sK1),X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK0),k3_tmap_1(X4,sK0,sK1,X5,k4_tmap_1(sK0,sK1)),X6)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f232,f49])).
% 2.21/0.65  fof(f232,plain,(
% 2.21/0.65    ( ! [X6,X4,X5] : (~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X4) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X4) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X5,sK1) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,X5,sK1,k4_tmap_1(sK0,sK1),X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK0),k3_tmap_1(X4,sK0,sK1,X5,k4_tmap_1(sK0,sK1)),X6)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f231,f53])).
% 2.21/0.65  fof(f231,plain,(
% 2.21/0.65    ( ! [X6,X4,X5] : (~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~l1_pre_topc(sK0) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X4) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X4) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X5,sK1) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,X5,sK1,k4_tmap_1(sK0,sK1),X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK0),k3_tmap_1(X4,sK0,sK1,X5,k4_tmap_1(sK0,sK1)),X6)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f230,f52])).
% 2.21/0.65  fof(f230,plain,(
% 2.21/0.65    ( ! [X6,X4,X5] : (~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X4) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X4) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X5,sK1) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,X5,sK1,k4_tmap_1(sK0,sK1),X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK0),k3_tmap_1(X4,sK0,sK1,X5,k4_tmap_1(sK0,sK1)),X6)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f210,f51])).
% 2.21/0.65  fof(f210,plain,(
% 2.21/0.65    ( ! [X6,X4,X5] : (~v2_pre_topc(X4) | ~l1_pre_topc(X4) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X5) | ~m1_pre_topc(X5,X4) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X4) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X4) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X5,sK1) | ~v1_funct_1(X6) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,X5,sK1,k4_tmap_1(sK0,sK1),X6),u1_struct_0(X5)) | r2_funct_2(u1_struct_0(X5),u1_struct_0(sK0),k3_tmap_1(X4,sK0,sK1,X5,k4_tmap_1(sK0,sK1)),X6)) )),
% 2.21/0.65    inference(resolution,[],[f91,f58])).
% 2.21/0.65  fof(f58,plain,(
% 2.21/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | r2_hidden(sK3(X1,X2,X3,X4,X5),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f24])).
% 2.21/0.65  fof(f1502,plain,(
% 2.21/0.65    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.21/0.65    inference(resolution,[],[f1498,f261])).
% 2.21/0.65  fof(f261,plain,(
% 2.21/0.65    ( ! [X16] : (~m1_subset_1(X16,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f260,f94])).
% 2.21/0.65  fof(f260,plain,(
% 2.21/0.65    ( ! [X16] : (~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X16,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f259,f166])).
% 2.21/0.65  fof(f166,plain,(
% 2.21/0.65    ~v1_xboole_0(u1_struct_0(sK1))),
% 2.21/0.65    inference(subsumption_resolution,[],[f165,f49])).
% 2.21/0.65  fof(f165,plain,(
% 2.21/0.65    v2_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1))),
% 2.21/0.65    inference(resolution,[],[f105,f73])).
% 2.21/0.65  fof(f73,plain,(
% 2.21/0.65    ( ! [X0] : (~l1_struct_0(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 2.21/0.65    inference(cnf_transformation,[],[f42])).
% 2.21/0.65  fof(f42,plain,(
% 2.21/0.65    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.21/0.65    inference(flattening,[],[f41])).
% 2.21/0.65  fof(f41,plain,(
% 2.21/0.65    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.21/0.65    inference(ennf_transformation,[],[f6])).
% 2.21/0.65  fof(f6,axiom,(
% 2.21/0.65    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 2.21/0.65  fof(f105,plain,(
% 2.21/0.65    l1_struct_0(sK1)),
% 2.21/0.65    inference(resolution,[],[f104,f74])).
% 2.21/0.65  fof(f74,plain,(
% 2.21/0.65    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f43])).
% 2.21/0.65  fof(f43,plain,(
% 2.21/0.65    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.21/0.65    inference(ennf_transformation,[],[f4])).
% 2.21/0.65  fof(f4,axiom,(
% 2.21/0.65    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.21/0.65  fof(f259,plain,(
% 2.21/0.65    ( ! [X16] : (v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X16,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f215,f88])).
% 2.21/0.65  fof(f215,plain,(
% 2.21/0.65    ( ! [X16] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X16,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16)) )),
% 2.21/0.65    inference(resolution,[],[f91,f64])).
% 2.21/0.65  fof(f64,plain,(
% 2.21/0.65    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f30])).
% 2.21/0.65  fof(f30,plain,(
% 2.21/0.65    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.21/0.65    inference(flattening,[],[f29])).
% 2.21/0.65  fof(f29,plain,(
% 2.21/0.65    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.21/0.65    inference(ennf_transformation,[],[f2])).
% 2.21/0.65  fof(f2,axiom,(
% 2.21/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 2.21/0.65  fof(f1500,plain,(
% 2.21/0.65    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.21/0.65    inference(subsumption_resolution,[],[f1437,f48])).
% 2.21/0.65  fof(f1437,plain,(
% 2.21/0.65    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.21/0.65    inference(backward_demodulation,[],[f1198,f1408])).
% 2.21/0.65  fof(f1198,plain,(
% 2.21/0.65    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)),
% 2.21/0.65    inference(subsumption_resolution,[],[f1197,f52])).
% 2.21/0.65  fof(f1197,plain,(
% 2.21/0.65    ~v2_pre_topc(sK0) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)),
% 2.21/0.65    inference(subsumption_resolution,[],[f1196,f51])).
% 2.21/0.65  fof(f1196,plain,(
% 2.21/0.65    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)),
% 2.21/0.65    inference(subsumption_resolution,[],[f1194,f53])).
% 2.21/0.65  fof(f1194,plain,(
% 2.21/0.65    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)),
% 2.21/0.65    inference(resolution,[],[f667,f50])).
% 2.21/0.65  fof(f667,plain,(
% 2.21/0.65    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f666,f47])).
% 2.21/0.65  fof(f666,plain,(
% 2.21/0.65    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f665,f45])).
% 2.21/0.65  fof(f665,plain,(
% 2.21/0.65    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | v2_struct_0(X0) | ~v1_funct_1(sK2) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f664,f106])).
% 2.21/0.65  fof(f664,plain,(
% 2.21/0.65    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | v2_struct_0(X0) | ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f659,f49])).
% 2.21/0.65  fof(f659,plain,(
% 2.21/0.65    ( ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | v2_struct_0(X0) | ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k3_tmap_1(X0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),sK2)) )),
% 2.21/0.65    inference(resolution,[],[f243,f46])).
% 2.21/0.65  fof(f243,plain,(
% 2.21/0.65    ( ! [X8,X7,X9] : (~v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0)) | ~l1_pre_topc(X7) | v2_struct_0(X8) | ~m1_pre_topc(sK1,X7) | v2_struct_0(X7) | ~m1_pre_topc(X8,sK1) | ~v1_funct_1(X9) | ~v2_pre_topc(X7) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) != k1_funct_1(X9,sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) | r2_funct_2(u1_struct_0(X8),u1_struct_0(sK0),k3_tmap_1(X7,sK0,sK1,X8,k4_tmap_1(sK0,sK1)),X9)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f242,f67])).
% 2.21/0.65  fof(f242,plain,(
% 2.21/0.65    ( ! [X8,X7,X9] : (~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v2_struct_0(X8) | ~m1_pre_topc(X8,X7) | ~m1_pre_topc(sK1,X7) | v2_struct_0(X7) | ~m1_pre_topc(X8,sK1) | ~v1_funct_1(X9) | ~v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) != k1_funct_1(X9,sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) | r2_funct_2(u1_struct_0(X8),u1_struct_0(sK0),k3_tmap_1(X7,sK0,sK1,X8,k4_tmap_1(sK0,sK1)),X9)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f241,f94])).
% 2.21/0.65  fof(f241,plain,(
% 2.21/0.65    ( ! [X8,X7,X9] : (~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v2_struct_0(X8) | ~m1_pre_topc(X8,X7) | ~m1_pre_topc(sK1,X7) | v2_struct_0(X7) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X8,sK1) | ~v1_funct_1(X9) | ~v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) != k1_funct_1(X9,sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) | r2_funct_2(u1_struct_0(X8),u1_struct_0(sK0),k3_tmap_1(X7,sK0,sK1,X8,k4_tmap_1(sK0,sK1)),X9)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f240,f88])).
% 2.21/0.65  fof(f240,plain,(
% 2.21/0.65    ( ! [X8,X7,X9] : (~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v2_struct_0(X8) | ~m1_pre_topc(X8,X7) | ~m1_pre_topc(sK1,X7) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X7) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X8,sK1) | ~v1_funct_1(X9) | ~v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) != k1_funct_1(X9,sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) | r2_funct_2(u1_struct_0(X8),u1_struct_0(sK0),k3_tmap_1(X7,sK0,sK1,X8,k4_tmap_1(sK0,sK1)),X9)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f239,f49])).
% 2.21/0.65  fof(f239,plain,(
% 2.21/0.65    ( ! [X8,X7,X9] : (~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v2_struct_0(X8) | ~m1_pre_topc(X8,X7) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X7) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X7) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X8,sK1) | ~v1_funct_1(X9) | ~v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) != k1_funct_1(X9,sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) | r2_funct_2(u1_struct_0(X8),u1_struct_0(sK0),k3_tmap_1(X7,sK0,sK1,X8,k4_tmap_1(sK0,sK1)),X9)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f238,f53])).
% 2.21/0.65  fof(f238,plain,(
% 2.21/0.65    ( ! [X8,X7,X9] : (~v2_pre_topc(X7) | ~l1_pre_topc(X7) | ~l1_pre_topc(sK0) | v2_struct_0(X8) | ~m1_pre_topc(X8,X7) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X7) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X7) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X8,sK1) | ~v1_funct_1(X9) | ~v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) != k1_funct_1(X9,sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) | r2_funct_2(u1_struct_0(X8),u1_struct_0(sK0),k3_tmap_1(X7,sK0,sK1,X8,k4_tmap_1(sK0,sK1)),X9)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f237,f52])).
% 2.21/0.65  fof(f237,plain,(
% 2.21/0.65    ( ! [X8,X7,X9] : (~v2_pre_topc(X7) | ~l1_pre_topc(X7) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X8) | ~m1_pre_topc(X8,X7) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X7) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X7) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X8,sK1) | ~v1_funct_1(X9) | ~v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) != k1_funct_1(X9,sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) | r2_funct_2(u1_struct_0(X8),u1_struct_0(sK0),k3_tmap_1(X7,sK0,sK1,X8,k4_tmap_1(sK0,sK1)),X9)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f211,f51])).
% 2.21/0.65  fof(f211,plain,(
% 2.21/0.65    ( ! [X8,X7,X9] : (~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X8) | ~m1_pre_topc(X8,X7) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X7) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X7) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X8,sK1) | ~v1_funct_1(X9) | ~v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK0)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) != k1_funct_1(X9,sK3(sK0,X8,sK1,k4_tmap_1(sK0,sK1),X9)) | r2_funct_2(u1_struct_0(X8),u1_struct_0(sK0),k3_tmap_1(X7,sK0,sK1,X8,k4_tmap_1(sK0,sK1)),X9)) )),
% 2.21/0.65    inference(resolution,[],[f91,f59])).
% 2.21/0.65  fof(f59,plain,(
% 2.21/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,sK3(X1,X2,X3,X4,X5)) != k1_funct_1(X5,sK3(X1,X2,X3,X4,X5)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f24])).
% 2.21/0.65  fof(f1518,plain,(
% 2.21/0.65    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.21/0.65    inference(subsumption_resolution,[],[f1510,f1504])).
% 2.21/0.65  fof(f1510,plain,(
% 2.21/0.65    ~m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0)) | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.21/0.65    inference(resolution,[],[f1499,f44])).
% 2.21/0.65  fof(f44,plain,(
% 2.21/0.65    ( ! [X3] : (~r2_hidden(X3,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k1_funct_1(sK2,X3) = X3) )),
% 2.21/0.65    inference(cnf_transformation,[],[f18])).
% 2.21/0.65  % SZS output end Proof for theBenchmark
% 2.21/0.65  % (18342)------------------------------
% 2.21/0.65  % (18342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.65  % (18342)Termination reason: Refutation
% 2.21/0.65  
% 2.21/0.65  % (18342)Memory used [KB]: 7164
% 2.21/0.65  % (18342)Time elapsed: 0.218 s
% 2.21/0.65  % (18342)------------------------------
% 2.21/0.65  % (18342)------------------------------
% 2.21/0.65  % (18336)Success in time 0.289 s
%------------------------------------------------------------------------------
