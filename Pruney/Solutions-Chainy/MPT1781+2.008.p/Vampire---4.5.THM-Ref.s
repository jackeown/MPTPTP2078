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
% DateTime   : Thu Dec  3 13:19:17 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  238 (13399 expanded)
%              Number of leaves         :   18 (2377 expanded)
%              Depth                    :   38
%              Number of atoms          : 1338 (107098 expanded)
%              Number of equality atoms :   95 (7882 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1707,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1706,f1705])).

fof(f1705,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f1590,f1704])).

fof(f1704,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f1597,f1703])).

fof(f1703,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f1701,f1586])).

fof(f1586,plain,(
    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1567,f57])).

fof(f57,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f1567,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f1194,f1547])).

fof(f1547,plain,(
    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f1546,f525])).

fof(f525,plain,(
    m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f293,f186])).

fof(f186,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f117,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f117,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f98,f62])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f98,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f59,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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

fof(f59,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f293,plain,(
    ! [X9] :
      ( ~ l1_struct_0(X9)
      | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f292,f107])).

fof(f107,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f106,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f106,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f105,f62])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f93,f61])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f93,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f59,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(f292,plain,(
    ! [X9] :
      ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X9)
      | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f291,f186])).

fof(f291,plain,(
    ! [X9] :
      ( ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X9)
      | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f290,f101])).

fof(f101,plain,(
    v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f100,f60])).

fof(f100,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f99,f62])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f91,f61])).

fof(f91,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f59,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_1(k4_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f290,plain,(
    ! [X9] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X9)
      | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f247,f89])).

fof(f89,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f62,f86])).

fof(f247,plain,(
    ! [X9] :
      ( ~ l1_struct_0(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X9)
      | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f104,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f104,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f103,f60])).

fof(f103,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f102,f62])).

fof(f102,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f92,f61])).

fof(f92,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f59,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1546,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f1545,f1539])).

fof(f1539,plain,(
    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1538,f1014])).

fof(f1014,plain,(
    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) ),
    inference(resolution,[],[f301,f187])).

fof(f187,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f117,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f301,plain,(
    ! [X10] :
      ( ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f300,f107])).

fof(f300,plain,(
    ! [X10] :
      ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f299,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f299,plain,(
    ! [X10] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f298,f101])).

fof(f298,plain,(
    ! [X10] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f297,f62])).

fof(f297,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f296,f61])).

fof(f296,plain,(
    ! [X10] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f295,f60])).

fof(f295,plain,(
    ! [X10] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f294,f117])).

fof(f294,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f248,f116])).

fof(f116,plain,(
    v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f115,f61])).

fof(f115,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f97,f62])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK1) ),
    inference(resolution,[],[f59,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f248,plain,(
    ! [X10] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X10,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10)) ) ),
    inference(resolution,[],[f104,f83])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f1538,plain,(
    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f1060,f187])).

fof(f1060,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1059,f60])).

fof(f1059,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1058,f61])).

fof(f1058,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1056,f62])).

fof(f1056,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f307,f59])).

fof(f307,plain,(
    ! [X12,X11] :
      ( ~ m1_pre_topc(sK1,X11)
      | ~ l1_pre_topc(X11)
      | ~ v2_pre_topc(X11)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X12,sK1)
      | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12)) ) ),
    inference(subsumption_resolution,[],[f306,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f306,plain,(
    ! [X12,X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(sK1,X11)
      | ~ m1_pre_topc(X12,X11)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X12,sK1)
      | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12)) ) ),
    inference(subsumption_resolution,[],[f305,f107])).

fof(f305,plain,(
    ! [X12,X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(sK1,X11)
      | ~ m1_pre_topc(X12,X11)
      | v2_struct_0(X11)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X12,sK1)
      | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12)) ) ),
    inference(subsumption_resolution,[],[f304,f101])).

fof(f304,plain,(
    ! [X12,X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(sK1,X11)
      | ~ m1_pre_topc(X12,X11)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X11)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X12,sK1)
      | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12)) ) ),
    inference(subsumption_resolution,[],[f303,f62])).

fof(f303,plain,(
    ! [X12,X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X11)
      | ~ m1_pre_topc(X12,X11)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X11)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X12,sK1)
      | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12)) ) ),
    inference(subsumption_resolution,[],[f302,f61])).

fof(f302,plain,(
    ! [X12,X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X11)
      | ~ m1_pre_topc(X12,X11)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X11)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X12,sK1)
      | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12)) ) ),
    inference(subsumption_resolution,[],[f249,f60])).

fof(f249,plain,(
    ! [X12,X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X11)
      | ~ m1_pre_topc(X12,X11)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X11)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X12,sK1)
      | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12)) ) ),
    inference(resolution,[],[f104,f84])).

fof(f84,plain,(
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
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f1545,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f1544,f463])).

fof(f463,plain,(
    v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f289,f186])).

fof(f289,plain,(
    ! [X8] :
      ( ~ l1_struct_0(X8)
      | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f288,f107])).

fof(f288,plain,(
    ! [X8] :
      ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X8)
      | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f287,f186])).

fof(f287,plain,(
    ! [X8] :
      ( ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X8)
      | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f286,f101])).

fof(f286,plain,(
    ! [X8] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X8)
      | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f246,f89])).

fof(f246,plain,(
    ! [X8] :
      ( ~ l1_struct_0(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X8)
      | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f104,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1544,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f1543,f1539])).

fof(f1543,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f1542,f456])).

fof(f456,plain,(
    v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)) ),
    inference(resolution,[],[f285,f186])).

fof(f285,plain,(
    ! [X7] :
      ( ~ l1_struct_0(X7)
      | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7)) ) ),
    inference(subsumption_resolution,[],[f284,f107])).

fof(f284,plain,(
    ! [X7] :
      ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X7)
      | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7)) ) ),
    inference(subsumption_resolution,[],[f283,f186])).

fof(f283,plain,(
    ! [X7] :
      ( ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X7)
      | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7)) ) ),
    inference(subsumption_resolution,[],[f282,f101])).

fof(f282,plain,(
    ! [X7] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X7)
      | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7)) ) ),
    inference(subsumption_resolution,[],[f245,f89])).

fof(f245,plain,(
    ! [X7] :
      ( ~ l1_struct_0(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ l1_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ l1_struct_0(X7)
      | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7)) ) ),
    inference(resolution,[],[f104,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1542,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1))
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f1540,f1539])).

fof(f1540,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f1425,f1539])).

fof(f1425,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1424,f101])).

fof(f1424,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1423,f107])).

fof(f1423,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1422,f104])).

fof(f1422,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f1028,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f1028,plain,(
    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1027,f60])).

fof(f1027,plain,
    ( v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1026,f61])).

fof(f1026,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1024,f62])).

fof(f1024,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f281,f59])).

fof(f281,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(sK1,X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f280,f107])).

fof(f280,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK1,X6)
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f279,f101])).

fof(f279,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f278,f58])).

fof(f278,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f277,f62])).

fof(f277,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f276,f61])).

fof(f276,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f244,f60])).

fof(f244,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(resolution,[],[f104,f68])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f1194,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1193,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f1193,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1192,f58])).

fof(f1192,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1191,f54])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f1191,plain,
    ( ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1182,f187])).

fof(f1182,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(resolution,[],[f267,f55])).

fof(f55,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f267,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(X3)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f266,f107])).

fof(f266,plain,(
    ! [X2,X3] :
      ( v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f265,f60])).

fof(f265,plain,(
    ! [X2,X3] :
      ( v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f264,f101])).

fof(f264,plain,(
    ! [X2,X3] :
      ( v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f263,f117])).

fof(f263,plain,(
    ! [X2,X3] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f262,f116])).

fof(f262,plain,(
    ! [X2,X3] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f261,f58])).

fof(f261,plain,(
    ! [X2,X3] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f260,f62])).

fof(f260,plain,(
    ! [X2,X3] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f242,f61])).

fof(f242,plain,(
    ! [X2,X3] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(resolution,[],[f104,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(X3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
                             => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).

fof(f1701,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f1604,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f110,f60])).

fof(f110,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f109,f58])).

fof(f109,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f108,f62])).

fof(f108,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f94,f61])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(resolution,[],[f59,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f1604,plain,(
    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f1586,f237])).

fof(f237,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f112,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f112,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f95,f62])).

fof(f95,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f59,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f1597,plain,(
    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f1585,f310])).

fof(f310,plain,(
    ! [X13] :
      ( ~ m1_subset_1(X13,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X13) = k1_funct_1(k4_tmap_1(sK0,sK1),X13) ) ),
    inference(subsumption_resolution,[],[f309,f107])).

fof(f309,plain,(
    ! [X13] :
      ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_subset_1(X13,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X13) = k1_funct_1(k4_tmap_1(sK0,sK1),X13) ) ),
    inference(subsumption_resolution,[],[f308,f192])).

fof(f192,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f191,f58])).

fof(f191,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f186,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
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

fof(f308,plain,(
    ! [X13] :
      ( v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_subset_1(X13,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X13) = k1_funct_1(k4_tmap_1(sK0,sK1),X13) ) ),
    inference(subsumption_resolution,[],[f250,f101])).

fof(f250,plain,(
    ! [X13] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_subset_1(X13,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X13) = k1_funct_1(k4_tmap_1(sK0,sK1),X13) ) ),
    inference(resolution,[],[f104,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f1585,plain,(
    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1564,f57])).

fof(f1564,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f1160,f1547])).

fof(f1160,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1159,f56])).

fof(f1159,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1158,f58])).

fof(f1158,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1157,f54])).

fof(f1157,plain,
    ( ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1148,f187])).

fof(f1148,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(resolution,[],[f259,f55])).

fof(f259,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f258,f107])).

fof(f258,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f257,f60])).

fof(f257,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f256,f101])).

fof(f256,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f255,f117])).

fof(f255,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f254,f116])).

fof(f254,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f253,f58])).

fof(f253,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f252,f62])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f241,f61])).

fof(f241,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(resolution,[],[f104,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(X3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1590,plain,(
    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f1574,f57])).

fof(f1574,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f1354,f1547])).

fof(f1354,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1353,f56])).

fof(f1353,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1352,f58])).

fof(f1352,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1351,f54])).

fof(f1351,plain,
    ( ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1342,f187])).

fof(f1342,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(resolution,[],[f275,f55])).

fof(f275,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(X5)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f274,f107])).

fof(f274,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f273,f60])).

fof(f273,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f272,f101])).

fof(f272,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f271,f117])).

fof(f271,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f270,f116])).

fof(f270,plain,(
    ! [X4,X5] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f269,f58])).

fof(f269,plain,(
    ! [X4,X5] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f268,f62])).

fof(f268,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f243,f61])).

fof(f243,plain,(
    ! [X4,X5] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(resolution,[],[f104,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(X3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1706,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f1702,f1586])).

fof(f1702,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f1604,f53])).

fof(f53,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3 ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:36:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (19852)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (19849)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (19869)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.50  % (19861)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (19857)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (19853)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (19850)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (19847)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (19858)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (19868)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (19860)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (19865)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (19867)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (19846)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (19855)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (19846)Refutation not found, incomplete strategy% (19846)------------------------------
% 0.22/0.53  % (19846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (19848)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (19851)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (19846)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (19846)Memory used [KB]: 10618
% 0.22/0.53  % (19846)Time elapsed: 0.117 s
% 0.22/0.53  % (19846)------------------------------
% 0.22/0.53  % (19846)------------------------------
% 0.22/0.53  % (19863)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (19871)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.53  % (19864)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.54  % (19866)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.54  % (19859)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (19854)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.54  % (19856)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.55  % (19862)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (19870)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 2.23/0.67  % (19851)Refutation found. Thanks to Tanya!
% 2.23/0.67  % SZS status Theorem for theBenchmark
% 2.23/0.67  % SZS output start Proof for theBenchmark
% 2.23/0.67  fof(f1707,plain,(
% 2.23/0.67    $false),
% 2.23/0.67    inference(subsumption_resolution,[],[f1706,f1705])).
% 2.23/0.67  fof(f1705,plain,(
% 2.23/0.67    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.23/0.67    inference(backward_demodulation,[],[f1590,f1704])).
% 2.23/0.67  fof(f1704,plain,(
% 2.23/0.67    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.23/0.67    inference(backward_demodulation,[],[f1597,f1703])).
% 2.23/0.67  fof(f1703,plain,(
% 2.23/0.67    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.23/0.67    inference(subsumption_resolution,[],[f1701,f1586])).
% 2.23/0.67  fof(f1586,plain,(
% 2.23/0.67    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.23/0.67    inference(subsumption_resolution,[],[f1567,f57])).
% 2.23/0.67  fof(f57,plain,(
% 2.23/0.67    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 2.23/0.67    inference(cnf_transformation,[],[f22])).
% 2.23/0.67  fof(f22,plain,(
% 2.23/0.67    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.23/0.67    inference(flattening,[],[f21])).
% 2.23/0.67  fof(f21,plain,(
% 2.23/0.67    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.23/0.67    inference(ennf_transformation,[],[f20])).
% 2.23/0.67  fof(f20,negated_conjecture,(
% 2.23/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 2.23/0.67    inference(negated_conjecture,[],[f19])).
% 2.23/0.67  fof(f19,conjecture,(
% 2.23/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).
% 2.23/0.67  fof(f1567,plain,(
% 2.23/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.23/0.67    inference(backward_demodulation,[],[f1194,f1547])).
% 2.23/0.67  fof(f1547,plain,(
% 2.23/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)),
% 2.23/0.67    inference(subsumption_resolution,[],[f1546,f525])).
% 2.23/0.67  fof(f525,plain,(
% 2.23/0.67    m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.23/0.67    inference(resolution,[],[f293,f186])).
% 2.23/0.67  fof(f186,plain,(
% 2.23/0.67    l1_struct_0(sK1)),
% 2.23/0.67    inference(resolution,[],[f117,f86])).
% 2.23/0.67  fof(f86,plain,(
% 2.23/0.67    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f52])).
% 2.23/0.67  fof(f52,plain,(
% 2.23/0.67    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.23/0.67    inference(ennf_transformation,[],[f5])).
% 2.23/0.67  fof(f5,axiom,(
% 2.23/0.67    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.23/0.67  fof(f117,plain,(
% 2.23/0.67    l1_pre_topc(sK1)),
% 2.23/0.67    inference(subsumption_resolution,[],[f98,f62])).
% 2.23/0.67  fof(f62,plain,(
% 2.23/0.67    l1_pre_topc(sK0)),
% 2.23/0.67    inference(cnf_transformation,[],[f22])).
% 2.23/0.67  fof(f98,plain,(
% 2.23/0.67    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 2.23/0.67    inference(resolution,[],[f59,f78])).
% 2.23/0.67  fof(f78,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f42])).
% 2.23/0.67  fof(f42,plain,(
% 2.23/0.67    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.23/0.67    inference(ennf_transformation,[],[f6])).
% 2.23/0.67  fof(f6,axiom,(
% 2.23/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.23/0.67  fof(f59,plain,(
% 2.23/0.67    m1_pre_topc(sK1,sK0)),
% 2.23/0.67    inference(cnf_transformation,[],[f22])).
% 2.23/0.67  fof(f293,plain,(
% 2.23/0.67    ( ! [X9] : (~l1_struct_0(X9) | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0))))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f292,f107])).
% 2.23/0.67  fof(f107,plain,(
% 2.23/0.67    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.23/0.67    inference(subsumption_resolution,[],[f106,f60])).
% 2.23/0.67  fof(f60,plain,(
% 2.23/0.67    ~v2_struct_0(sK0)),
% 2.23/0.67    inference(cnf_transformation,[],[f22])).
% 2.23/0.67  fof(f106,plain,(
% 2.23/0.67    v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.23/0.67    inference(subsumption_resolution,[],[f105,f62])).
% 2.23/0.67  fof(f105,plain,(
% 2.23/0.67    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.23/0.67    inference(subsumption_resolution,[],[f93,f61])).
% 2.23/0.67  fof(f61,plain,(
% 2.23/0.67    v2_pre_topc(sK0)),
% 2.23/0.67    inference(cnf_transformation,[],[f22])).
% 2.23/0.67  fof(f93,plain,(
% 2.23/0.67    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.23/0.67    inference(resolution,[],[f59,f71])).
% 2.23/0.67  fof(f71,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f30])).
% 2.23/0.67  fof(f30,plain,(
% 2.23/0.67    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.67    inference(flattening,[],[f29])).
% 2.23/0.67  fof(f29,plain,(
% 2.23/0.67    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.67    inference(ennf_transformation,[],[f11])).
% 2.23/0.67  fof(f11,axiom,(
% 2.23/0.67    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 2.23/0.67  fof(f292,plain,(
% 2.23/0.67    ( ! [X9] : (~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X9) | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0))))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f291,f186])).
% 2.23/0.67  fof(f291,plain,(
% 2.23/0.67    ( ! [X9] : (~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X9) | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0))))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f290,f101])).
% 2.23/0.67  fof(f101,plain,(
% 2.23/0.67    v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.23/0.67    inference(subsumption_resolution,[],[f100,f60])).
% 2.23/0.67  fof(f100,plain,(
% 2.23/0.67    v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.23/0.67    inference(subsumption_resolution,[],[f99,f62])).
% 2.23/0.67  fof(f99,plain,(
% 2.23/0.67    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.23/0.67    inference(subsumption_resolution,[],[f91,f61])).
% 2.23/0.67  fof(f91,plain,(
% 2.23/0.67    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.23/0.67    inference(resolution,[],[f59,f69])).
% 2.23/0.67  fof(f69,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_1(k4_tmap_1(X0,X1))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f30])).
% 2.23/0.67  fof(f290,plain,(
% 2.23/0.67    ( ! [X9] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X9) | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0))))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f247,f89])).
% 2.23/0.67  fof(f89,plain,(
% 2.23/0.67    l1_struct_0(sK0)),
% 2.23/0.67    inference(resolution,[],[f62,f86])).
% 2.23/0.67  fof(f247,plain,(
% 2.23/0.67    ( ! [X9] : (~l1_struct_0(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X9) | m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK0))))) )),
% 2.23/0.67    inference(resolution,[],[f104,f82])).
% 2.23/0.67  fof(f82,plain,(
% 2.23/0.67    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f45])).
% 2.23/0.67  fof(f45,plain,(
% 2.23/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 2.23/0.67    inference(flattening,[],[f44])).
% 2.23/0.67  fof(f44,plain,(
% 2.23/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 2.23/0.67    inference(ennf_transformation,[],[f10])).
% 2.23/0.67  fof(f10,axiom,(
% 2.23/0.67    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 2.23/0.67  fof(f104,plain,(
% 2.23/0.67    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.23/0.67    inference(subsumption_resolution,[],[f103,f60])).
% 2.23/0.67  fof(f103,plain,(
% 2.23/0.67    v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.23/0.67    inference(subsumption_resolution,[],[f102,f62])).
% 2.23/0.67  fof(f102,plain,(
% 2.23/0.67    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.23/0.67    inference(subsumption_resolution,[],[f92,f61])).
% 2.23/0.67  fof(f92,plain,(
% 2.23/0.67    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.23/0.67    inference(resolution,[],[f59,f70])).
% 2.23/0.67  fof(f70,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f30])).
% 2.23/0.67  fof(f1546,plain,(
% 2.23/0.67    ~m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)),
% 2.23/0.67    inference(forward_demodulation,[],[f1545,f1539])).
% 2.23/0.67  fof(f1539,plain,(
% 2.23/0.67    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.23/0.67    inference(forward_demodulation,[],[f1538,f1014])).
% 2.23/0.67  fof(f1014,plain,(
% 2.23/0.67    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1))),
% 2.23/0.67    inference(resolution,[],[f301,f187])).
% 2.23/0.67  fof(f187,plain,(
% 2.23/0.67    m1_pre_topc(sK1,sK1)),
% 2.23/0.67    inference(resolution,[],[f117,f79])).
% 2.23/0.67  fof(f79,plain,(
% 2.23/0.67    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f43])).
% 2.23/0.67  fof(f43,plain,(
% 2.23/0.67    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.23/0.67    inference(ennf_transformation,[],[f13])).
% 2.23/0.67  fof(f13,axiom,(
% 2.23/0.67    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.23/0.67  fof(f301,plain,(
% 2.23/0.67    ( ! [X10] : (~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f300,f107])).
% 2.23/0.67  fof(f300,plain,(
% 2.23/0.67    ( ! [X10] : (~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f299,f58])).
% 2.23/0.67  fof(f58,plain,(
% 2.23/0.67    ~v2_struct_0(sK1)),
% 2.23/0.67    inference(cnf_transformation,[],[f22])).
% 2.23/0.67  fof(f299,plain,(
% 2.23/0.67    ( ! [X10] : (v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f298,f101])).
% 2.23/0.67  fof(f298,plain,(
% 2.23/0.67    ( ! [X10] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f297,f62])).
% 2.23/0.67  fof(f297,plain,(
% 2.23/0.67    ( ! [X10] : (~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f296,f61])).
% 2.23/0.67  fof(f296,plain,(
% 2.23/0.67    ( ! [X10] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f295,f60])).
% 2.23/0.67  fof(f295,plain,(
% 2.23/0.67    ( ! [X10] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f294,f117])).
% 2.23/0.67  fof(f294,plain,(
% 2.23/0.67    ( ! [X10] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f248,f116])).
% 2.23/0.67  fof(f116,plain,(
% 2.23/0.67    v2_pre_topc(sK1)),
% 2.23/0.67    inference(subsumption_resolution,[],[f115,f61])).
% 2.23/0.67  fof(f115,plain,(
% 2.23/0.67    ~v2_pre_topc(sK0) | v2_pre_topc(sK1)),
% 2.23/0.67    inference(subsumption_resolution,[],[f97,f62])).
% 2.23/0.67  fof(f97,plain,(
% 2.23/0.67    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK1)),
% 2.23/0.67    inference(resolution,[],[f59,f77])).
% 2.23/0.67  fof(f77,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f41])).
% 2.23/0.67  fof(f41,plain,(
% 2.23/0.67    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.23/0.67    inference(flattening,[],[f40])).
% 2.23/0.67  fof(f40,plain,(
% 2.23/0.67    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.23/0.67    inference(ennf_transformation,[],[f4])).
% 2.23/0.67  fof(f4,axiom,(
% 2.23/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 2.23/0.67  fof(f248,plain,(
% 2.23/0.67    ( ! [X10] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X10,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X10) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X10))) )),
% 2.23/0.67    inference(resolution,[],[f104,f83])).
% 2.23/0.67  fof(f83,plain,(
% 2.23/0.67    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f47])).
% 2.23/0.67  fof(f47,plain,(
% 2.23/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.67    inference(flattening,[],[f46])).
% 2.23/0.67  fof(f46,plain,(
% 2.23/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.67    inference(ennf_transformation,[],[f8])).
% 2.23/0.67  fof(f8,axiom,(
% 2.23/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 2.23/0.67  fof(f1538,plain,(
% 2.23/0.67    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.23/0.67    inference(resolution,[],[f1060,f187])).
% 2.23/0.67  fof(f1060,plain,(
% 2.23/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f1059,f60])).
% 2.23/0.67  fof(f1059,plain,(
% 2.23/0.67    ( ! [X0] : (v2_struct_0(sK0) | ~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f1058,f61])).
% 2.23/0.67  fof(f1058,plain,(
% 2.23/0.67    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f1056,f62])).
% 2.23/0.67  fof(f1056,plain,(
% 2.23/0.67    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 2.23/0.67    inference(resolution,[],[f307,f59])).
% 2.23/0.67  fof(f307,plain,(
% 2.23/0.67    ( ! [X12,X11] : (~m1_pre_topc(sK1,X11) | ~l1_pre_topc(X11) | ~v2_pre_topc(X11) | v2_struct_0(X11) | ~m1_pre_topc(X12,sK1) | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f306,f76])).
% 2.23/0.67  fof(f76,plain,(
% 2.23/0.67    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f39])).
% 2.23/0.67  fof(f39,plain,(
% 2.23/0.67    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.23/0.67    inference(flattening,[],[f38])).
% 2.23/0.67  fof(f38,plain,(
% 2.23/0.67    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.23/0.67    inference(ennf_transformation,[],[f17])).
% 2.23/0.67  fof(f17,axiom,(
% 2.23/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 2.23/0.67  fof(f306,plain,(
% 2.23/0.67    ( ! [X12,X11] : (~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~m1_pre_topc(sK1,X11) | ~m1_pre_topc(X12,X11) | v2_struct_0(X11) | ~m1_pre_topc(X12,sK1) | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f305,f107])).
% 2.23/0.67  fof(f305,plain,(
% 2.23/0.67    ( ! [X12,X11] : (~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~m1_pre_topc(sK1,X11) | ~m1_pre_topc(X12,X11) | v2_struct_0(X11) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X12,sK1) | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f304,f101])).
% 2.23/0.67  fof(f304,plain,(
% 2.23/0.67    ( ! [X12,X11] : (~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~m1_pre_topc(sK1,X11) | ~m1_pre_topc(X12,X11) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X11) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X12,sK1) | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f303,f62])).
% 2.23/0.67  fof(f303,plain,(
% 2.23/0.67    ( ! [X12,X11] : (~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X11) | ~m1_pre_topc(X12,X11) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X11) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X12,sK1) | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f302,f61])).
% 2.23/0.67  fof(f302,plain,(
% 2.23/0.67    ( ! [X12,X11] : (~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X11) | ~m1_pre_topc(X12,X11) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X11) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X12,sK1) | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f249,f60])).
% 2.23/0.67  fof(f249,plain,(
% 2.23/0.67    ( ! [X12,X11] : (~v2_pre_topc(X11) | ~l1_pre_topc(X11) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X11) | ~m1_pre_topc(X12,X11) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X11) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X12,sK1) | k3_tmap_1(X11,sK0,sK1,X12,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X12))) )),
% 2.23/0.67    inference(resolution,[],[f104,f84])).
% 2.23/0.67  fof(f84,plain,(
% 2.23/0.67    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f49])).
% 2.23/0.67  fof(f49,plain,(
% 2.23/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.67    inference(flattening,[],[f48])).
% 2.23/0.67  fof(f48,plain,(
% 2.23/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.67    inference(ennf_transformation,[],[f9])).
% 2.23/0.67  fof(f9,axiom,(
% 2.23/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 2.23/0.67  fof(f1545,plain,(
% 2.23/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.23/0.67    inference(subsumption_resolution,[],[f1544,f463])).
% 2.23/0.67  fof(f463,plain,(
% 2.23/0.67    v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.23/0.67    inference(resolution,[],[f289,f186])).
% 2.23/0.67  fof(f289,plain,(
% 2.23/0.67    ( ! [X8] : (~l1_struct_0(X8) | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f288,f107])).
% 2.23/0.67  fof(f288,plain,(
% 2.23/0.67    ( ! [X8] : (~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X8) | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f287,f186])).
% 2.23/0.67  fof(f287,plain,(
% 2.23/0.67    ( ! [X8] : (~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X8) | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f286,f101])).
% 2.23/0.67  fof(f286,plain,(
% 2.23/0.67    ( ! [X8] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X8) | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f246,f89])).
% 2.23/0.67  fof(f246,plain,(
% 2.23/0.67    ( ! [X8] : (~l1_struct_0(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X8) | v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X8),u1_struct_0(X8),u1_struct_0(sK0))) )),
% 2.23/0.67    inference(resolution,[],[f104,f81])).
% 2.23/0.67  fof(f81,plain,(
% 2.23/0.67    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f45])).
% 2.23/0.67  fof(f1544,plain,(
% 2.23/0.67    ~v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.23/0.67    inference(forward_demodulation,[],[f1543,f1539])).
% 2.23/0.67  fof(f1543,plain,(
% 2.23/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.23/0.67    inference(subsumption_resolution,[],[f1542,f456])).
% 2.23/0.67  fof(f456,plain,(
% 2.23/0.67    v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1))),
% 2.23/0.67    inference(resolution,[],[f285,f186])).
% 2.23/0.67  fof(f285,plain,(
% 2.23/0.67    ( ! [X7] : (~l1_struct_0(X7) | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f284,f107])).
% 2.23/0.67  fof(f284,plain,(
% 2.23/0.67    ( ! [X7] : (~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X7) | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f283,f186])).
% 2.23/0.67  fof(f283,plain,(
% 2.23/0.67    ( ! [X7] : (~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X7) | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f282,f101])).
% 2.23/0.67  fof(f282,plain,(
% 2.23/0.67    ( ! [X7] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X7) | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f245,f89])).
% 2.23/0.67  fof(f245,plain,(
% 2.23/0.67    ( ! [X7] : (~l1_struct_0(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~l1_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_struct_0(X7) | v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7))) )),
% 2.23/0.67    inference(resolution,[],[f104,f80])).
% 2.23/0.67  fof(f80,plain,(
% 2.23/0.67    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f45])).
% 2.23/0.67  fof(f1542,plain,(
% 2.23/0.67    ~v1_funct_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)) | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.23/0.67    inference(forward_demodulation,[],[f1540,f1539])).
% 2.23/0.67  fof(f1540,plain,(
% 2.23/0.67    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) | ~v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.23/0.67    inference(backward_demodulation,[],[f1425,f1539])).
% 2.23/0.67  fof(f1425,plain,(
% 2.23/0.67    ~v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.23/0.67    inference(subsumption_resolution,[],[f1424,f101])).
% 2.23/0.67  fof(f1424,plain,(
% 2.23/0.67    ~v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.23/0.67    inference(subsumption_resolution,[],[f1423,f107])).
% 2.23/0.67  fof(f1423,plain,(
% 2.23/0.67    ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.23/0.67    inference(subsumption_resolution,[],[f1422,f104])).
% 2.23/0.67  fof(f1422,plain,(
% 2.23/0.67    ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.23/0.67    inference(resolution,[],[f1028,f64])).
% 2.23/0.67  fof(f64,plain,(
% 2.23/0.67    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~v1_funct_1(X2)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f24])).
% 2.23/0.67  fof(f24,plain,(
% 2.23/0.67    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.23/0.67    inference(flattening,[],[f23])).
% 2.23/0.67  fof(f23,plain,(
% 2.23/0.67    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.23/0.67    inference(ennf_transformation,[],[f3])).
% 2.23/0.67  fof(f3,axiom,(
% 2.23/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.23/0.67  fof(f1028,plain,(
% 2.23/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.23/0.67    inference(subsumption_resolution,[],[f1027,f60])).
% 2.23/0.67  fof(f1027,plain,(
% 2.23/0.67    v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.23/0.67    inference(subsumption_resolution,[],[f1026,f61])).
% 2.23/0.67  fof(f1026,plain,(
% 2.23/0.67    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.23/0.67    inference(subsumption_resolution,[],[f1024,f62])).
% 2.23/0.67  fof(f1024,plain,(
% 2.23/0.67    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.23/0.67    inference(resolution,[],[f281,f59])).
% 2.23/0.67  fof(f281,plain,(
% 2.23/0.67    ( ! [X6] : (~m1_pre_topc(sK1,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f280,f107])).
% 2.23/0.67  fof(f280,plain,(
% 2.23/0.67    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK1,X6) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f279,f101])).
% 2.23/0.67  fof(f279,plain,(
% 2.23/0.67    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f278,f58])).
% 2.23/0.67  fof(f278,plain,(
% 2.23/0.67    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f277,f62])).
% 2.23/0.67  fof(f277,plain,(
% 2.23/0.67    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f276,f61])).
% 2.23/0.67  fof(f276,plain,(
% 2.23/0.67    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f244,f60])).
% 2.23/0.67  fof(f244,plain,(
% 2.23/0.67    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.23/0.67    inference(resolution,[],[f104,f68])).
% 2.23/0.67  fof(f68,plain,(
% 2.23/0.67    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f28])).
% 2.23/0.67  fof(f28,plain,(
% 2.23/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.67    inference(flattening,[],[f27])).
% 2.23/0.67  fof(f27,plain,(
% 2.23/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.67    inference(ennf_transformation,[],[f16])).
% 2.23/0.67  fof(f16,axiom,(
% 2.23/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).
% 2.23/0.67  fof(f1194,plain,(
% 2.23/0.67    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.23/0.67    inference(subsumption_resolution,[],[f1193,f56])).
% 2.23/0.67  fof(f56,plain,(
% 2.23/0.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.23/0.67    inference(cnf_transformation,[],[f22])).
% 2.23/0.67  fof(f1193,plain,(
% 2.23/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.23/0.67    inference(subsumption_resolution,[],[f1192,f58])).
% 2.23/0.67  fof(f1192,plain,(
% 2.23/0.67    v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.23/0.67    inference(subsumption_resolution,[],[f1191,f54])).
% 2.23/0.67  fof(f54,plain,(
% 2.23/0.67    v1_funct_1(sK2)),
% 2.23/0.67    inference(cnf_transformation,[],[f22])).
% 2.23/0.67  fof(f1191,plain,(
% 2.23/0.67    ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.23/0.67    inference(subsumption_resolution,[],[f1182,f187])).
% 2.23/0.67  fof(f1182,plain,(
% 2.23/0.67    ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.23/0.67    inference(resolution,[],[f267,f55])).
% 2.23/0.67  fof(f55,plain,(
% 2.23/0.67    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.23/0.67    inference(cnf_transformation,[],[f22])).
% 2.23/0.67  fof(f267,plain,(
% 2.23/0.67    ( ! [X2,X3] : (~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | v2_struct_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f266,f107])).
% 2.23/0.67  fof(f266,plain,(
% 2.23/0.67    ( ! [X2,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f265,f60])).
% 2.23/0.67  fof(f265,plain,(
% 2.23/0.67    ( ! [X2,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f264,f101])).
% 2.23/0.67  fof(f264,plain,(
% 2.23/0.67    ( ! [X2,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f263,f117])).
% 2.23/0.67  fof(f263,plain,(
% 2.23/0.67    ( ! [X2,X3] : (~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f262,f116])).
% 2.23/0.67  fof(f262,plain,(
% 2.23/0.67    ( ! [X2,X3] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f261,f58])).
% 2.23/0.67  fof(f261,plain,(
% 2.23/0.67    ( ! [X2,X3] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f260,f62])).
% 2.23/0.67  fof(f260,plain,(
% 2.23/0.67    ( ! [X2,X3] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f242,f61])).
% 2.23/0.67  fof(f242,plain,(
% 2.23/0.67    ( ! [X2,X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.23/0.67    inference(resolution,[],[f104,f66])).
% 2.23/0.67  fof(f66,plain,(
% 2.23/0.67    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f26])).
% 2.23/0.67  fof(f26,plain,(
% 2.23/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.67    inference(flattening,[],[f25])).
% 2.23/0.67  fof(f25,plain,(
% 2.23/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.67    inference(ennf_transformation,[],[f15])).
% 2.23/0.67  fof(f15,axiom,(
% 2.23/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).
% 2.23/0.67  fof(f1701,plain,(
% 2.23/0.67    ~r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.23/0.67    inference(resolution,[],[f1604,f111])).
% 2.23/0.67  fof(f111,plain,(
% 2.23/0.67    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f110,f60])).
% 2.23/0.67  fof(f110,plain,(
% 2.23/0.67    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f109,f58])).
% 2.23/0.67  fof(f109,plain,(
% 2.23/0.67    ( ! [X0] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f108,f62])).
% 2.23/0.67  fof(f108,plain,(
% 2.23/0.67    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f94,f61])).
% 2.23/0.67  fof(f94,plain,(
% 2.23/0.67    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.23/0.67    inference(resolution,[],[f59,f72])).
% 2.23/0.67  fof(f72,plain,(
% 2.23/0.67    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2) )),
% 2.23/0.67    inference(cnf_transformation,[],[f32])).
% 2.23/0.67  fof(f32,plain,(
% 2.23/0.67    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.67    inference(flattening,[],[f31])).
% 2.23/0.67  fof(f31,plain,(
% 2.23/0.67    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.67    inference(ennf_transformation,[],[f18])).
% 2.23/0.67  fof(f18,axiom,(
% 2.23/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).
% 2.23/0.67  fof(f1604,plain,(
% 2.23/0.67    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))),
% 2.23/0.67    inference(resolution,[],[f1586,f237])).
% 2.23/0.67  fof(f237,plain,(
% 2.23/0.67    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1)) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 2.23/0.67    inference(resolution,[],[f112,f74])).
% 2.23/0.67  fof(f74,plain,(
% 2.23/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f36])).
% 2.23/0.67  fof(f36,plain,(
% 2.23/0.67    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.23/0.67    inference(flattening,[],[f35])).
% 2.23/0.67  fof(f35,plain,(
% 2.23/0.67    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.23/0.67    inference(ennf_transformation,[],[f1])).
% 2.23/0.67  fof(f1,axiom,(
% 2.23/0.67    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 2.23/0.67  fof(f112,plain,(
% 2.23/0.67    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.23/0.67    inference(subsumption_resolution,[],[f95,f62])).
% 2.23/0.67  fof(f95,plain,(
% 2.23/0.67    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.23/0.67    inference(resolution,[],[f59,f75])).
% 2.23/0.67  fof(f75,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f37])).
% 2.23/0.67  fof(f37,plain,(
% 2.23/0.67    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.23/0.67    inference(ennf_transformation,[],[f12])).
% 2.23/0.67  fof(f12,axiom,(
% 2.23/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 2.23/0.67  fof(f1597,plain,(
% 2.23/0.67    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.23/0.67    inference(resolution,[],[f1585,f310])).
% 2.23/0.67  fof(f310,plain,(
% 2.23/0.67    ( ! [X13] : (~m1_subset_1(X13,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X13) = k1_funct_1(k4_tmap_1(sK0,sK1),X13)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f309,f107])).
% 2.23/0.67  fof(f309,plain,(
% 2.23/0.67    ( ! [X13] : (~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X13,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X13) = k1_funct_1(k4_tmap_1(sK0,sK1),X13)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f308,f192])).
% 2.23/0.67  fof(f192,plain,(
% 2.23/0.67    ~v1_xboole_0(u1_struct_0(sK1))),
% 2.23/0.67    inference(subsumption_resolution,[],[f191,f58])).
% 2.23/0.67  fof(f191,plain,(
% 2.23/0.67    v2_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1))),
% 2.23/0.67    inference(resolution,[],[f186,f85])).
% 2.23/0.67  fof(f85,plain,(
% 2.23/0.67    ( ! [X0] : (~l1_struct_0(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f51])).
% 2.23/0.67  fof(f51,plain,(
% 2.23/0.67    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.23/0.67    inference(flattening,[],[f50])).
% 2.23/0.67  fof(f50,plain,(
% 2.23/0.67    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.23/0.67    inference(ennf_transformation,[],[f7])).
% 2.23/0.67  fof(f7,axiom,(
% 2.23/0.67    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 2.23/0.67  fof(f308,plain,(
% 2.23/0.67    ( ! [X13] : (v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X13,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X13) = k1_funct_1(k4_tmap_1(sK0,sK1),X13)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f250,f101])).
% 2.23/0.67  fof(f250,plain,(
% 2.23/0.67    ( ! [X13] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X13,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X13) = k1_funct_1(k4_tmap_1(sK0,sK1),X13)) )),
% 2.23/0.67    inference(resolution,[],[f104,f73])).
% 2.23/0.67  fof(f73,plain,(
% 2.23/0.67    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f34])).
% 2.23/0.67  fof(f34,plain,(
% 2.23/0.67    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.23/0.67    inference(flattening,[],[f33])).
% 2.23/0.67  fof(f33,plain,(
% 2.23/0.67    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.23/0.67    inference(ennf_transformation,[],[f2])).
% 2.23/0.67  fof(f2,axiom,(
% 2.23/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 2.23/0.67  fof(f1585,plain,(
% 2.23/0.67    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.23/0.67    inference(subsumption_resolution,[],[f1564,f57])).
% 2.23/0.67  fof(f1564,plain,(
% 2.23/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.23/0.67    inference(backward_demodulation,[],[f1160,f1547])).
% 2.23/0.67  fof(f1160,plain,(
% 2.23/0.67    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.23/0.67    inference(subsumption_resolution,[],[f1159,f56])).
% 2.23/0.67  fof(f1159,plain,(
% 2.23/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.23/0.67    inference(subsumption_resolution,[],[f1158,f58])).
% 2.23/0.67  fof(f1158,plain,(
% 2.23/0.67    v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.23/0.67    inference(subsumption_resolution,[],[f1157,f54])).
% 2.23/0.67  fof(f1157,plain,(
% 2.23/0.67    ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.23/0.67    inference(subsumption_resolution,[],[f1148,f187])).
% 2.23/0.67  fof(f1148,plain,(
% 2.23/0.67    ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.23/0.67    inference(resolution,[],[f259,f55])).
% 2.23/0.67  fof(f259,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(X1) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f258,f107])).
% 2.23/0.67  fof(f258,plain,(
% 2.23/0.67    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f257,f60])).
% 2.23/0.67  fof(f257,plain,(
% 2.23/0.67    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f256,f101])).
% 2.23/0.67  fof(f256,plain,(
% 2.23/0.67    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f255,f117])).
% 2.23/0.67  fof(f255,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f254,f116])).
% 2.23/0.67  fof(f254,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f253,f58])).
% 2.23/0.67  fof(f253,plain,(
% 2.23/0.67    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f252,f62])).
% 2.23/0.67  fof(f252,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f241,f61])).
% 2.23/0.67  fof(f241,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.23/0.67    inference(resolution,[],[f104,f65])).
% 2.23/0.67  fof(f65,plain,(
% 2.23/0.67    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f26])).
% 2.23/0.67  fof(f1590,plain,(
% 2.23/0.67    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.23/0.67    inference(subsumption_resolution,[],[f1574,f57])).
% 2.23/0.67  fof(f1574,plain,(
% 2.23/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.23/0.67    inference(backward_demodulation,[],[f1354,f1547])).
% 2.23/0.67  fof(f1354,plain,(
% 2.23/0.67    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.23/0.67    inference(subsumption_resolution,[],[f1353,f56])).
% 2.23/0.67  fof(f1353,plain,(
% 2.23/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.23/0.67    inference(subsumption_resolution,[],[f1352,f58])).
% 2.23/0.67  fof(f1352,plain,(
% 2.23/0.67    v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.23/0.67    inference(subsumption_resolution,[],[f1351,f54])).
% 2.23/0.67  fof(f1351,plain,(
% 2.23/0.67    ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.23/0.67    inference(subsumption_resolution,[],[f1342,f187])).
% 2.23/0.67  fof(f1342,plain,(
% 2.23/0.67    ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.23/0.67    inference(resolution,[],[f275,f55])).
% 2.23/0.67  fof(f275,plain,(
% 2.23/0.67    ( ! [X4,X5] : (~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(X5) | v2_struct_0(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f274,f107])).
% 2.23/0.67  fof(f274,plain,(
% 2.23/0.67    ( ! [X4,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f273,f60])).
% 2.23/0.67  fof(f273,plain,(
% 2.23/0.67    ( ! [X4,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f272,f101])).
% 2.23/0.67  fof(f272,plain,(
% 2.23/0.67    ( ! [X4,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f271,f117])).
% 2.23/0.67  fof(f271,plain,(
% 2.23/0.67    ( ! [X4,X5] : (~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f270,f116])).
% 2.23/0.67  fof(f270,plain,(
% 2.23/0.67    ( ! [X4,X5] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f269,f58])).
% 2.23/0.67  fof(f269,plain,(
% 2.23/0.67    ( ! [X4,X5] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f268,f62])).
% 2.23/0.67  fof(f268,plain,(
% 2.23/0.67    ( ! [X4,X5] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f243,f61])).
% 2.23/0.67  fof(f243,plain,(
% 2.23/0.67    ( ! [X4,X5] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.23/0.67    inference(resolution,[],[f104,f67])).
% 2.23/0.67  fof(f67,plain,(
% 2.23/0.67    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f26])).
% 2.23/0.67  fof(f1706,plain,(
% 2.23/0.67    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.23/0.67    inference(subsumption_resolution,[],[f1702,f1586])).
% 2.23/0.67  fof(f1702,plain,(
% 2.23/0.67    ~r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.23/0.67    inference(resolution,[],[f1604,f53])).
% 2.23/0.67  fof(f53,plain,(
% 2.23/0.67    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3) )),
% 2.23/0.67    inference(cnf_transformation,[],[f22])).
% 2.23/0.67  % SZS output end Proof for theBenchmark
% 2.23/0.67  % (19851)------------------------------
% 2.23/0.67  % (19851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.67  % (19851)Termination reason: Refutation
% 2.23/0.67  
% 2.23/0.67  % (19851)Memory used [KB]: 7036
% 2.23/0.67  % (19851)Time elapsed: 0.232 s
% 2.23/0.67  % (19851)------------------------------
% 2.23/0.67  % (19851)------------------------------
% 2.23/0.67  % (19845)Success in time 0.309 s
%------------------------------------------------------------------------------
