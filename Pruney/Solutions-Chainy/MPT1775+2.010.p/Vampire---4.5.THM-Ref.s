%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 520 expanded)
%              Number of leaves         :   13 (  92 expanded)
%              Depth                    :   54
%              Number of atoms          :  983 (6619 expanded)
%              Number of equality atoms :   17 ( 293 expanded)
%              Maximal formula depth    :   32 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f523,plain,(
    $false ),
    inference(subsumption_resolution,[],[f522,f77])).

fof(f77,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f37,f38])).

fof(f38,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
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
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & v1_tsep_1(X2,X3) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X1,X4,X5)
                                    <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f37,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f522,plain,(
    ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f521,f323])).

fof(f323,plain,(
    ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f322,f268])).

fof(f268,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f251,f54])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f251,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f48,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f48,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f322,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f96,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f96,plain,
    ( ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f47,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f521,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[],[f520,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f520,plain,(
    ~ r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f518,f268])).

fof(f518,plain,
    ( ~ r2_hidden(sK5,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f517,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f517,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f516,f378])).

fof(f378,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f188,f220])).

fof(f220,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f203,f54])).

fof(f203,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f46,f57])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f188,plain,
    ( ~ l1_pre_topc(sK3)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f44,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f44,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f516,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[],[f514,f43])).

fof(f43,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f514,plain,(
    ! [X0] :
      ( ~ v1_tsep_1(X0,sK3)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(X0,sK2)
      | ~ r2_hidden(sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f513,f432])).

fof(f432,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | m1_pre_topc(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f430,f268])).

fof(f430,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f429,f56])).

fof(f429,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(subsumption_resolution,[],[f428,f268])).

fof(f428,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(sK2)
      | ~ m1_pre_topc(X1,sK2)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(subsumption_resolution,[],[f427,f271])).

fof(f271,plain,(
    v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f270,f54])).

fof(f270,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f254,f53])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f254,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(resolution,[],[f48,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f427,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,sK3)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | ~ m1_pre_topc(X1,sK2)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(subsumption_resolution,[],[f426,f223])).

fof(f223,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f222,f54])).

fof(f222,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f206,f53])).

% (24090)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f206,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[],[f46,f64])).

fof(f426,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK3)
      | m1_pre_topc(X0,sK3)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | ~ m1_pre_topc(X1,sK2)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(subsumption_resolution,[],[f425,f220])).

fof(f425,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | m1_pre_topc(X0,sK3)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | ~ m1_pre_topc(X1,sK2)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f190,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f190,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | m1_pre_topc(X0,sK3) ) ),
    inference(resolution,[],[f44,f65])).

fof(f513,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5,u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(X0,sK2)
      | ~ v1_tsep_1(X0,sK3)
      | ~ m1_pre_topc(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f512,f220])).

fof(f512,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5,u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK3)
      | ~ v1_tsep_1(X0,sK3)
      | ~ m1_pre_topc(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f511,f223])).

fof(f511,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5,u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(X0,sK2)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v1_tsep_1(X0,sK3)
      | ~ m1_pre_topc(X0,sK3) ) ),
    inference(duplicate_literal_removal,[],[f510])).

fof(f510,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5,u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(X0,sK2)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v1_tsep_1(X0,sK3)
      | ~ m1_pre_topc(X0,sK3) ) ),
    inference(resolution,[],[f488,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f488,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(u1_struct_0(X0),sK3)
      | ~ r2_hidden(sK5,u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f487,f268])).

fof(f487,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(u1_struct_0(X0),sK3)
      | ~ r2_hidden(sK5,u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ l1_pre_topc(sK2)
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(resolution,[],[f456,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f456,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(subsumption_resolution,[],[f455,f77])).

fof(f455,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f454,f39])).

fof(f39,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f454,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f453,f44])).

fof(f453,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f452,f42])).

fof(f42,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f452,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f451,f41])).

fof(f41,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f451,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f450,f40])).

fof(f40,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f450,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f449,f46])).

fof(f449,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f448,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f448,plain,(
    ! [X0] :
      ( v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f447,f48])).

fof(f447,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f446,f47])).

fof(f446,plain,(
    ! [X0] :
      ( v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f445,f51])).

fof(f51,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f445,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f444,f50])).

fof(f50,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f444,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f443,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f443,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f442,f54])).

fof(f442,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f441,f53])).

fof(f441,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f440,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f440,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f439,f407])).

fof(f407,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(subsumption_resolution,[],[f406,f44])).

fof(f406,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f405,f77])).

fof(f405,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f404,f39])).

fof(f404,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f403,f42])).

fof(f403,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f402,f41])).

fof(f402,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f401,f40])).

fof(f401,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f400,f48])).

fof(f400,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f399,f47])).

fof(f399,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f398,f46])).

fof(f398,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f397,f45])).

fof(f397,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f396,f51])).

fof(f396,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f395,f50])).

fof(f395,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f394,f49])).

fof(f394,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f393,f54])).

fof(f393,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f392,f53])).

fof(f392,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f391,f52])).

fof(f391,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f387])).

fof(f387,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(resolution,[],[f78,f74])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
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
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
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
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | X5 != X6
      | ~ m1_pre_topc(X3,X2)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

fof(f78,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(forward_demodulation,[],[f36,f38])).

fof(f36,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f16])).

fof(f439,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK1,sK4,sK5)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f436])).

fof(f436,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK1,sK4,sK5)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ v3_pre_topc(X0,sK3)
      | ~ r2_hidden(sK5,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK3,sK1,sK4,sK5) ) ),
    inference(resolution,[],[f79,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
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
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ v3_pre_topc(X5,X3)
      | ~ r2_hidden(X7,X5)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X7) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v2_struct_0(X0)
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
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ v3_pre_topc(X5,X3)
      | ~ r2_hidden(X6,X5)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | X6 != X7
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X6) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

fof(f79,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(forward_demodulation,[],[f35,f38])).

fof(f35,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (24091)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (24101)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (24096)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (24106)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.49  % (24101)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f523,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f522,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.49    inference(forward_demodulation,[],[f37,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    sK5 = sK6),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f13])).
% 0.22/0.49  fof(f13,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f522,plain,(
% 0.22/0.49    ~m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.49    inference(subsumption_resolution,[],[f521,f323])).
% 0.22/0.49  fof(f323,plain,(
% 0.22/0.49    ~v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.49    inference(subsumption_resolution,[],[f322,f268])).
% 0.22/0.49  fof(f268,plain,(
% 0.22/0.49    l1_pre_topc(sK2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f251,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f251,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.22/0.49    inference(resolution,[],[f48,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    m1_pre_topc(sK2,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f322,plain,(
% 0.22/0.49    ~v1_xboole_0(u1_struct_0(sK2)) | ~l1_pre_topc(sK2)),
% 0.22/0.49    inference(resolution,[],[f96,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ~l1_struct_0(sK2) | ~v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.49    inference(resolution,[],[f47,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ~v2_struct_0(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f521,plain,(
% 0.22/0.49    v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.49    inference(resolution,[],[f520,f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.49  fof(f520,plain,(
% 0.22/0.49    ~r2_hidden(sK5,u1_struct_0(sK2))),
% 0.22/0.49    inference(subsumption_resolution,[],[f518,f268])).
% 0.22/0.49  fof(f518,plain,(
% 0.22/0.49    ~r2_hidden(sK5,u1_struct_0(sK2)) | ~l1_pre_topc(sK2)),
% 0.22/0.49    inference(resolution,[],[f517,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.49  fof(f517,plain,(
% 0.22/0.49    ~m1_pre_topc(sK2,sK2) | ~r2_hidden(sK5,u1_struct_0(sK2))),
% 0.22/0.49    inference(subsumption_resolution,[],[f516,f378])).
% 0.22/0.49  fof(f378,plain,(
% 0.22/0.49    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.49    inference(resolution,[],[f188,f220])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    l1_pre_topc(sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f203,f54])).
% 0.22/0.49  fof(f203,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.22/0.49    inference(resolution,[],[f46,f57])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    m1_pre_topc(sK3,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    ~l1_pre_topc(sK3) | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.49    inference(resolution,[],[f44,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f516,plain,(
% 0.22/0.49    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK2) | ~r2_hidden(sK5,u1_struct_0(sK2))),
% 0.22/0.49    inference(resolution,[],[f514,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    v1_tsep_1(sK2,sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f514,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_tsep_1(X0,sK3) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK2) | ~r2_hidden(sK5,u1_struct_0(X0))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f513,f432])).
% 0.22/0.49  fof(f432,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_pre_topc(X0,sK3)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f430,f268])).
% 0.22/0.49  fof(f430,plain,(
% 0.22/0.49    ( ! [X0] : (m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2)) )),
% 0.22/0.49    inference(resolution,[],[f429,f56])).
% 0.22/0.49  fof(f429,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,sK2) | m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f428,f268])).
% 0.22/0.49  fof(f428,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK2) | ~m1_pre_topc(X1,sK2) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f427,f271])).
% 0.22/0.49  fof(f271,plain,(
% 0.22/0.49    v2_pre_topc(sK2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f270,f54])).
% 0.22/0.49  fof(f270,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | v2_pre_topc(sK2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f254,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    v2_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f254,plain,(
% 0.22/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_pre_topc(sK2)),
% 0.22/0.49    inference(resolution,[],[f48,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.49  fof(f427,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_pre_topc(X0,sK3) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~m1_pre_topc(X1,sK2) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f426,f223])).
% 0.22/0.49  fof(f223,plain,(
% 0.22/0.49    v2_pre_topc(sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f222,f54])).
% 0.22/0.49  fof(f222,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f206,f53])).
% 0.22/0.49  % (24090)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  fof(f206,plain,(
% 0.22/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.22/0.49    inference(resolution,[],[f46,f64])).
% 0.22/0.49  fof(f426,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v2_pre_topc(sK3) | m1_pre_topc(X0,sK3) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~m1_pre_topc(X1,sK2) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f425,f220])).
% 0.22/0.49  fof(f425,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | m1_pre_topc(X0,sK3) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~m1_pre_topc(X1,sK2) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.49    inference(resolution,[],[f190,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.22/0.49  fof(f190,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | m1_pre_topc(X0,sK3)) )),
% 0.22/0.49    inference(resolution,[],[f44,f65])).
% 0.22/0.49  fof(f513,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(sK5,u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK2) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f512,f220])).
% 0.22/0.49  fof(f512,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(sK5,u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK3) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f511,f223])).
% 0.22/0.49  fof(f511,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(sK5,u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK2) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f510])).
% 0.22/0.49  fof(f510,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(sK5,u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK2) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) | ~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3)) )),
% 0.22/0.49    inference(resolution,[],[f488,f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.22/0.49  fof(f488,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_pre_topc(u1_struct_0(X0),sK3) | ~r2_hidden(sK5,u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK2)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f487,f268])).
% 0.22/0.49  fof(f487,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_pre_topc(u1_struct_0(X0),sK3) | ~r2_hidden(sK5,u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK2) | ~m1_pre_topc(X0,sK2)) )),
% 0.22/0.49    inference(resolution,[],[f456,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.22/0.49  fof(f456,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f455,f77])).
% 0.22/0.49  fof(f455,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f454,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f454,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f453,f44])).
% 0.22/0.49  fof(f453,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f452,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f452,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f451,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f451,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f450,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    v1_funct_1(sK4)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f450,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f449,f46])).
% 0.22/0.49  fof(f449,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f448,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ~v2_struct_0(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f448,plain,(
% 0.22/0.49    ( ! [X0] : (v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f447,f48])).
% 0.22/0.49  fof(f447,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f446,f47])).
% 0.22/0.49  fof(f446,plain,(
% 0.22/0.49    ( ! [X0] : (v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f445,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    l1_pre_topc(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f445,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f444,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    v2_pre_topc(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f444,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f443,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ~v2_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f443,plain,(
% 0.22/0.49    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f442,f54])).
% 0.22/0.49  fof(f442,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f441,f53])).
% 0.22/0.49  fof(f441,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f440,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f440,plain,(
% 0.22/0.49    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f439,f407])).
% 0.22/0.49  fof(f407,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.49    inference(subsumption_resolution,[],[f406,f44])).
% 0.22/0.49  fof(f406,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f405,f77])).
% 0.22/0.49  fof(f405,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f404,f39])).
% 0.22/0.49  fof(f404,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f403,f42])).
% 0.22/0.49  fof(f403,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f402,f41])).
% 0.22/0.49  fof(f402,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f401,f40])).
% 0.22/0.49  fof(f401,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f400,f48])).
% 0.22/0.49  fof(f400,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f399,f47])).
% 0.22/0.49  fof(f399,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f398,f46])).
% 0.22/0.49  fof(f398,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f397,f45])).
% 0.22/0.49  fof(f397,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f396,f51])).
% 0.22/0.49  fof(f396,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f395,f50])).
% 0.22/0.49  fof(f395,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f394,f49])).
% 0.22/0.49  fof(f394,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f393,f54])).
% 0.22/0.49  fof(f393,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f392,f53])).
% 0.22/0.49  fof(f392,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f391,f52])).
% 0.22/0.49  fof(f391,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f387])).
% 0.22/0.49  fof(f387,plain,(
% 0.22/0.49    ~r1_tmap_1(sK3,sK1,sK4,sK5) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.49    inference(resolution,[],[f78,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,X4,X6) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)) )),
% 0.22/0.49    inference(equality_resolution,[],[f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | X5 != X6 | ~m1_pre_topc(X3,X2) | ~r1_tmap_1(X2,X1,X4,X5) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.49    inference(forward_demodulation,[],[f36,f38])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f439,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tmap_1(sK3,sK1,sK4,sK5) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f436])).
% 0.22/0.49  fof(f436,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tmap_1(sK3,sK1,sK4,sK5) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK5,X0) | ~r1_tarski(X0,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK1,sK4,sK5)) )),
% 0.22/0.49    inference(resolution,[],[f79,f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~v3_pre_topc(X5,X3) | ~r2_hidden(X7,X5) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7)) )),
% 0.22/0.50    inference(equality_resolution,[],[f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~v3_pre_topc(X5,X3) | ~r2_hidden(X6,X5) | ~r1_tarski(X5,u1_struct_0(X2)) | X6 != X7 | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X6)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.50    inference(forward_demodulation,[],[f35,f38])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (24101)------------------------------
% 0.22/0.50  % (24101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24101)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (24101)Memory used [KB]: 1791
% 0.22/0.50  % (24101)Time elapsed: 0.019 s
% 0.22/0.50  % (24101)------------------------------
% 0.22/0.50  % (24101)------------------------------
% 0.22/0.50  % (24099)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (24082)Success in time 0.136 s
%------------------------------------------------------------------------------
