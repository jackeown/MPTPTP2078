%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:17 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  252 (19417 expanded)
%              Number of leaves         :   16 (3436 expanded)
%              Depth                    :   38
%              Number of atoms          : 1513 (156263 expanded)
%              Number of equality atoms :  100 (11458 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2620,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2619,f2618])).

fof(f2618,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f2163,f2617])).

fof(f2617,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f2616,f2299])).

fof(f2299,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f2162,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f2162,plain,(
    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f2129,f55])).

fof(f55,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

fof(f2129,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f903,f2125])).

fof(f2125,plain,(
    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f2096,f2124])).

fof(f2124,plain,(
    k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2123,f2059])).

fof(f2059,plain,(
    m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f2011,f2034])).

fof(f2034,plain,(
    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2033,f477])).

fof(f477,plain,(
    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) ),
    inference(resolution,[],[f287,f190])).

fof(f190,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f115,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f115,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f94,f60])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f57,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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

fof(f57,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f287,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f286,f103])).

fof(f103,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f102,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f102,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f101,f60])).

fof(f101,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f89,f59])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f57,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(f286,plain,(
    ! [X7] :
      ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f285,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f285,plain,(
    ! [X7] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f284,f97])).

fof(f97,plain,(
    v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f96,f58])).

fof(f96,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f95,f60])).

fof(f95,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f87,f59])).

fof(f87,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f57,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_1(k4_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f284,plain,(
    ! [X7] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f283,f60])).

fof(f283,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f282,f59])).

fof(f282,plain,(
    ! [X7] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f281,f58])).

fof(f281,plain,(
    ! [X7] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f280,f115])).

fof(f280,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f243,f114])).

fof(f114,plain,(
    v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f113,f59])).

fof(f113,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f93,f60])).

fof(f93,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK1) ),
    inference(resolution,[],[f57,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f243,plain,(
    ! [X7] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X7,sK1)
      | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7)) ) ),
    inference(resolution,[],[f100,f79])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f46])).

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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f100,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f99,f58])).

fof(f99,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f98,f60])).

fof(f98,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f88,f59])).

fof(f88,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f57,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2033,plain,(
    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f728,f190])).

fof(f728,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f727,f58])).

fof(f727,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f726,f59])).

fof(f726,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f724,f60])).

fof(f724,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f308,f57])).

fof(f308,plain,(
    ! [X14,X15] :
      ( ~ m1_pre_topc(sK1,X14)
      | ~ l1_pre_topc(X14)
      | ~ v2_pre_topc(X14)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(subsumption_resolution,[],[f307,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f307,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(subsumption_resolution,[],[f306,f103])).

fof(f306,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | v2_struct_0(X14)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(subsumption_resolution,[],[f305,f97])).

fof(f305,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X14)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(subsumption_resolution,[],[f304,f60])).

fof(f304,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X14)
      | ~ m1_pre_topc(X15,X14)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X14)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(subsumption_resolution,[],[f303,f59])).

fof(f303,plain,(
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
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(subsumption_resolution,[],[f247,f58])).

fof(f247,plain,(
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
      | ~ m1_pre_topc(X15,sK1)
      | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15)) ) ),
    inference(resolution,[],[f100,f83])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f2011,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f588,f57])).

fof(f588,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f587,f58])).

fof(f587,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f586,f59])).

fof(f586,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f584,f60])).

fof(f584,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f302,f57])).

fof(f302,plain,(
    ! [X12,X13] :
      ( ~ m1_pre_topc(sK1,X12)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | v2_struct_0(X12)
      | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f301,f103])).

fof(f301,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(sK1,X12)
      | ~ m1_pre_topc(X13,X12)
      | v2_struct_0(X12)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f300,f97])).

fof(f300,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(sK1,X12)
      | ~ m1_pre_topc(X13,X12)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X12)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f299,f60])).

fof(f299,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X12)
      | ~ m1_pre_topc(X13,X12)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X12)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f298,f59])).

fof(f298,plain,(
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
      | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f246,f58])).

fof(f246,plain,(
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
      | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f100,f82])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f2123,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2122,f2096])).

fof(f2122,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2099,f2038])).

fof(f2038,plain,(
    v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f998,f2034])).

fof(f998,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f545,f57])).

fof(f545,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f544,f58])).

fof(f544,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f543,f59])).

fof(f543,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f541,f60])).

fof(f541,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f297,f57])).

fof(f297,plain,(
    ! [X10,X11] :
      ( ~ m1_pre_topc(sK1,X10)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | v2_struct_0(X10)
      | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f296,f103])).

fof(f296,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(sK1,X10)
      | ~ m1_pre_topc(X11,X10)
      | v2_struct_0(X10)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f295,f97])).

fof(f295,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(sK1,X10)
      | ~ m1_pre_topc(X11,X10)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X10)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f294,f60])).

fof(f294,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X10)
      | ~ m1_pre_topc(X11,X10)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X10)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f293,f59])).

fof(f293,plain,(
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
      | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f245,f58])).

fof(f245,plain,(
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
      | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f100,f81])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f2099,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f992,f2096])).

fof(f992,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f991,f97])).

fof(f991,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f990,f514])).

fof(f514,plain,(
    v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f485,f190])).

fof(f485,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f484,f56])).

fof(f484,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(sK1)
      | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f483,f114])).

fof(f483,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(sK1)
      | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f479,f115])).

fof(f479,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(sK1)
      | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) ) ),
    inference(resolution,[],[f292,f190])).

fof(f292,plain,(
    ! [X8,X9] :
      ( ~ m1_pre_topc(sK1,X8)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | v2_struct_0(X8)
      | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f291,f103])).

fof(f291,plain,(
    ! [X8,X9] :
      ( ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(sK1,X8)
      | ~ m1_pre_topc(X9,X8)
      | v2_struct_0(X8)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f290,f97])).

fof(f290,plain,(
    ! [X8,X9] :
      ( ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(sK1,X8)
      | ~ m1_pre_topc(X9,X8)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X8)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f289,f60])).

fof(f289,plain,(
    ! [X8,X9] :
      ( ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X8)
      | ~ m1_pre_topc(X9,X8)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X8)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f288,f59])).

fof(f288,plain,(
    ! [X8,X9] :
      ( ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X8)
      | ~ m1_pre_topc(X9,X8)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X8)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f244,f58])).

fof(f244,plain,(
    ! [X8,X9] :
      ( ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,X8)
      | ~ m1_pre_topc(X9,X8)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X8)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1))) ) ),
    inference(resolution,[],[f100,f80])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f990,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f989,f103])).

fof(f989,plain,
    ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f988,f100])).

fof(f988,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f540,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f540,plain,(
    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f539,f56])).

fof(f539,plain,
    ( v2_struct_0(sK1)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f538,f114])).

fof(f538,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f534,f115])).

fof(f534,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f279,f190])).

fof(f279,plain,(
    ! [X6] :
      ( ~ m1_pre_topc(sK1,X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f278,f103])).

fof(f278,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK1,X6)
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f277,f97])).

fof(f277,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f276,f56])).

fof(f276,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X6)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v2_struct_0(X6)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f275,f60])).

fof(f275,plain,(
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
    inference(subsumption_resolution,[],[f274,f59])).

fof(f274,plain,(
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
    inference(subsumption_resolution,[],[f242,f58])).

fof(f242,plain,(
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
    inference(resolution,[],[f100,f66])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).

fof(f2096,plain,(
    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2095,f477])).

fof(f2095,plain,(
    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f731,f190])).

fof(f731,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f730,f56])).

fof(f730,plain,(
    ! [X1] :
      ( v2_struct_0(sK1)
      | ~ m1_pre_topc(X1,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f729,f114])).

fof(f729,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X1,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f725,f115])).

fof(f725,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X1,sK1)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f308,f190])).

fof(f903,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f902,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f902,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f901,f56])).

fof(f901,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f900,f52])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f900,plain,
    ( ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f894,f190])).

fof(f894,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(resolution,[],[f265,f53])).

fof(f53,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f265,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_funct_1(X3)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f264,f103])).

fof(f264,plain,(
    ! [X2,X3] :
      ( v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3) ) ),
    inference(subsumption_resolution,[],[f263,f58])).

fof(f263,plain,(
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
    inference(subsumption_resolution,[],[f262,f97])).

fof(f262,plain,(
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
    inference(subsumption_resolution,[],[f261,f115])).

fof(f261,plain,(
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
    inference(subsumption_resolution,[],[f260,f114])).

fof(f260,plain,(
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
    inference(subsumption_resolution,[],[f259,f56])).

fof(f259,plain,(
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
    inference(subsumption_resolution,[],[f258,f60])).

fof(f258,plain,(
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
    inference(subsumption_resolution,[],[f240,f59])).

fof(f240,plain,(
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
    inference(resolution,[],[f100,f64])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f25])).

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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

fof(f2616,plain,
    ( sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f2292,f2615])).

fof(f2615,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f2612,f2162])).

fof(f2612,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f2295,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f106,f58])).

fof(f106,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f105,f56])).

fof(f105,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f104,f60])).

fof(f104,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f90,f59])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(resolution,[],[f57,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).

fof(f2295,plain,(
    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f2161,f110])).

fof(f110,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f109,f58])).

fof(f109,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f108,f56])).

fof(f108,plain,(
    ! [X1] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f91,f60])).

fof(f91,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f57,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f2161,plain,(
    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f2127,f55])).

fof(f2127,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f875,f2125])).

fof(f875,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f874,f54])).

fof(f874,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f873,f56])).

fof(f873,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f872,f52])).

fof(f872,plain,
    ( ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f866,f190])).

fof(f866,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(resolution,[],[f257,f53])).

fof(f257,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_pre_topc(X0,sK1)
      | ~ v1_funct_1(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f256,f103])).

fof(f256,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
      | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1))
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1) ) ),
    inference(subsumption_resolution,[],[f255,f58])).

fof(f255,plain,(
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
    inference(subsumption_resolution,[],[f254,f97])).

fof(f254,plain,(
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
    inference(subsumption_resolution,[],[f253,f115])).

fof(f253,plain,(
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
    inference(subsumption_resolution,[],[f252,f114])).

fof(f252,plain,(
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
    inference(subsumption_resolution,[],[f251,f56])).

fof(f251,plain,(
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
    inference(subsumption_resolution,[],[f250,f60])).

fof(f250,plain,(
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
    inference(subsumption_resolution,[],[f239,f59])).

fof(f239,plain,(
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
    inference(resolution,[],[f100,f63])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f2292,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f2161,f310])).

fof(f310,plain,(
    ! [X16] :
      ( ~ m1_subset_1(X16,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16) ) ),
    inference(subsumption_resolution,[],[f309,f103])).

fof(f309,plain,(
    ! [X16] :
      ( v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16) ) ),
    inference(subsumption_resolution,[],[f248,f97])).

fof(f248,plain,(
    ! [X16] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16) ) ),
    inference(resolution,[],[f100,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f2163,plain,(
    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f2131,f55])).

fof(f2131,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f1213,f2125])).

fof(f1213,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1212,f54])).

fof(f1212,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1211,f56])).

fof(f1211,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1210,f52])).

fof(f1210,plain,
    ( ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(subsumption_resolution,[],[f1202,f190])).

fof(f1202,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v1_funct_1(sK2)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(resolution,[],[f273,f53])).

fof(f273,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_pre_topc(X4,sK1)
      | ~ v1_funct_1(X5)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f272,f103])).

fof(f272,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1)
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5) ) ),
    inference(subsumption_resolution,[],[f271,f58])).

fof(f271,plain,(
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
    inference(subsumption_resolution,[],[f270,f97])).

fof(f270,plain,(
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
    inference(subsumption_resolution,[],[f269,f115])).

fof(f269,plain,(
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
    inference(subsumption_resolution,[],[f268,f114])).

fof(f268,plain,(
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
    inference(subsumption_resolution,[],[f267,f56])).

fof(f267,plain,(
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
    inference(subsumption_resolution,[],[f266,f60])).

fof(f266,plain,(
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
    inference(subsumption_resolution,[],[f241,f59])).

fof(f241,plain,(
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
    inference(resolution,[],[f100,f65])).

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
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2619,plain,(
    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f2613,f2162])).

fof(f2613,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))
    | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f2295,f51])).

fof(f51,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3 ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.50  % (6906)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (6907)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (6914)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (6915)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (6899)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (6905)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (6896)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (6897)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (6900)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (6916)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (6917)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (6898)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (6895)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (6904)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.54  % (6909)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.54  % (6901)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.54  % (6919)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.54  % (6913)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.54  % (6894)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.54  % (6903)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  % (6912)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.54  % (6908)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (6918)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.55  % (6910)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (6894)Refutation not found, incomplete strategy% (6894)------------------------------
% 0.22/0.55  % (6894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (6894)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (6894)Memory used [KB]: 10618
% 0.22/0.55  % (6894)Time elapsed: 0.090 s
% 0.22/0.55  % (6894)------------------------------
% 0.22/0.55  % (6894)------------------------------
% 0.22/0.55  % (6902)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.55  % (6911)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 2.05/0.69  % (6899)Refutation found. Thanks to Tanya!
% 2.05/0.69  % SZS status Theorem for theBenchmark
% 2.05/0.69  % SZS output start Proof for theBenchmark
% 2.05/0.69  fof(f2620,plain,(
% 2.05/0.69    $false),
% 2.05/0.69    inference(subsumption_resolution,[],[f2619,f2618])).
% 2.05/0.69  fof(f2618,plain,(
% 2.05/0.69    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.05/0.69    inference(backward_demodulation,[],[f2163,f2617])).
% 2.05/0.69  fof(f2617,plain,(
% 2.05/0.69    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.05/0.69    inference(subsumption_resolution,[],[f2616,f2299])).
% 2.05/0.69  fof(f2299,plain,(
% 2.05/0.69    ~v1_xboole_0(u1_struct_0(sK1))),
% 2.05/0.69    inference(resolution,[],[f2162,f73])).
% 2.05/0.69  fof(f73,plain,(
% 2.05/0.69    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.05/0.69    inference(cnf_transformation,[],[f36])).
% 2.05/0.69  fof(f36,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.05/0.69    inference(ennf_transformation,[],[f19])).
% 2.05/0.69  fof(f19,plain,(
% 2.05/0.69    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.05/0.69    inference(unused_predicate_definition_removal,[],[f1])).
% 2.05/0.69  fof(f1,axiom,(
% 2.05/0.69    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.05/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.05/0.69  fof(f2162,plain,(
% 2.05/0.69    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.05/0.69    inference(subsumption_resolution,[],[f2129,f55])).
% 2.05/0.69  fof(f55,plain,(
% 2.05/0.69    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 2.05/0.69    inference(cnf_transformation,[],[f21])).
% 2.05/0.69  fof(f21,plain,(
% 2.05/0.69    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.69    inference(flattening,[],[f20])).
% 2.05/0.69  fof(f20,plain,(
% 2.05/0.69    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.05/0.69    inference(ennf_transformation,[],[f18])).
% 2.05/0.69  fof(f18,negated_conjecture,(
% 2.05/0.69    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 2.05/0.69    inference(negated_conjecture,[],[f17])).
% 2.05/0.69  fof(f17,conjecture,(
% 2.05/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 2.05/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).
% 2.05/0.69  fof(f2129,plain,(
% 2.05/0.69    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.05/0.69    inference(backward_demodulation,[],[f903,f2125])).
% 2.05/0.69  fof(f2125,plain,(
% 2.05/0.69    k4_tmap_1(sK0,sK1) = k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1)),
% 2.05/0.69    inference(backward_demodulation,[],[f2096,f2124])).
% 2.05/0.69  fof(f2124,plain,(
% 2.05/0.69    k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(subsumption_resolution,[],[f2123,f2059])).
% 2.05/0.69  fof(f2059,plain,(
% 2.05/0.69    m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.05/0.69    inference(backward_demodulation,[],[f2011,f2034])).
% 2.05/0.69  fof(f2034,plain,(
% 2.05/0.69    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(forward_demodulation,[],[f2033,f477])).
% 2.05/0.69  fof(f477,plain,(
% 2.05/0.69    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1))),
% 2.05/0.69    inference(resolution,[],[f287,f190])).
% 2.05/0.69  fof(f190,plain,(
% 2.05/0.69    m1_pre_topc(sK1,sK1)),
% 2.05/0.69    inference(resolution,[],[f115,f78])).
% 2.05/0.69  fof(f78,plain,(
% 2.05/0.69    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 2.05/0.69    inference(cnf_transformation,[],[f44])).
% 2.05/0.69  fof(f44,plain,(
% 2.05/0.69    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.05/0.69    inference(ennf_transformation,[],[f12])).
% 2.05/0.69  fof(f12,axiom,(
% 2.05/0.69    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.05/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.05/0.69  fof(f115,plain,(
% 2.05/0.69    l1_pre_topc(sK1)),
% 2.05/0.69    inference(subsumption_resolution,[],[f94,f60])).
% 2.05/0.69  fof(f60,plain,(
% 2.05/0.69    l1_pre_topc(sK0)),
% 2.05/0.69    inference(cnf_transformation,[],[f21])).
% 2.05/0.69  fof(f94,plain,(
% 2.05/0.69    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 2.05/0.69    inference(resolution,[],[f57,f77])).
% 2.05/0.69  fof(f77,plain,(
% 2.05/0.69    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 2.05/0.69    inference(cnf_transformation,[],[f43])).
% 2.05/0.69  fof(f43,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.05/0.69    inference(ennf_transformation,[],[f6])).
% 2.05/0.69  fof(f6,axiom,(
% 2.05/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.05/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.05/0.69  fof(f57,plain,(
% 2.05/0.69    m1_pre_topc(sK1,sK0)),
% 2.05/0.69    inference(cnf_transformation,[],[f21])).
% 2.05/0.69  fof(f287,plain,(
% 2.05/0.69    ( ! [X7] : (~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f286,f103])).
% 2.05/0.69  fof(f103,plain,(
% 2.05/0.69    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.05/0.69    inference(subsumption_resolution,[],[f102,f58])).
% 2.05/0.69  fof(f58,plain,(
% 2.05/0.69    ~v2_struct_0(sK0)),
% 2.05/0.69    inference(cnf_transformation,[],[f21])).
% 2.05/0.69  fof(f102,plain,(
% 2.05/0.69    v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.05/0.69    inference(subsumption_resolution,[],[f101,f60])).
% 2.05/0.69  fof(f101,plain,(
% 2.05/0.69    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.05/0.69    inference(subsumption_resolution,[],[f89,f59])).
% 2.05/0.69  fof(f59,plain,(
% 2.05/0.69    v2_pre_topc(sK0)),
% 2.05/0.69    inference(cnf_transformation,[],[f21])).
% 2.05/0.69  fof(f89,plain,(
% 2.05/0.69    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.05/0.69    inference(resolution,[],[f57,f69])).
% 2.05/0.69  fof(f69,plain,(
% 2.05/0.69    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 2.05/0.69    inference(cnf_transformation,[],[f29])).
% 2.05/0.69  fof(f29,plain,(
% 2.05/0.69    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.69    inference(flattening,[],[f28])).
% 2.05/0.69  fof(f28,plain,(
% 2.05/0.69    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.69    inference(ennf_transformation,[],[f11])).
% 2.05/0.69  fof(f11,axiom,(
% 2.05/0.69    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 2.05/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 2.05/0.69  fof(f286,plain,(
% 2.05/0.69    ( ! [X7] : (~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f285,f56])).
% 2.05/0.69  fof(f56,plain,(
% 2.05/0.69    ~v2_struct_0(sK1)),
% 2.05/0.69    inference(cnf_transformation,[],[f21])).
% 2.05/0.69  fof(f285,plain,(
% 2.05/0.69    ( ! [X7] : (v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f284,f97])).
% 2.05/0.69  fof(f97,plain,(
% 2.05/0.69    v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(subsumption_resolution,[],[f96,f58])).
% 2.05/0.69  fof(f96,plain,(
% 2.05/0.69    v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(subsumption_resolution,[],[f95,f60])).
% 2.05/0.69  fof(f95,plain,(
% 2.05/0.69    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(subsumption_resolution,[],[f87,f59])).
% 2.05/0.69  fof(f87,plain,(
% 2.05/0.69    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(resolution,[],[f57,f67])).
% 2.05/0.69  fof(f67,plain,(
% 2.05/0.69    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_1(k4_tmap_1(X0,X1))) )),
% 2.05/0.69    inference(cnf_transformation,[],[f29])).
% 2.05/0.69  fof(f284,plain,(
% 2.05/0.69    ( ! [X7] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f283,f60])).
% 2.05/0.69  fof(f283,plain,(
% 2.05/0.69    ( ! [X7] : (~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f282,f59])).
% 2.05/0.69  fof(f282,plain,(
% 2.05/0.69    ( ! [X7] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f281,f58])).
% 2.05/0.69  fof(f281,plain,(
% 2.05/0.69    ( ! [X7] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f280,f115])).
% 2.05/0.69  fof(f280,plain,(
% 2.05/0.69    ( ! [X7] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f243,f114])).
% 2.05/0.69  fof(f114,plain,(
% 2.05/0.69    v2_pre_topc(sK1)),
% 2.05/0.69    inference(subsumption_resolution,[],[f113,f59])).
% 2.05/0.69  fof(f113,plain,(
% 2.05/0.69    ~v2_pre_topc(sK0) | v2_pre_topc(sK1)),
% 2.05/0.69    inference(subsumption_resolution,[],[f93,f60])).
% 2.05/0.69  fof(f93,plain,(
% 2.05/0.69    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK1)),
% 2.05/0.69    inference(resolution,[],[f57,f76])).
% 2.05/0.69  fof(f76,plain,(
% 2.05/0.69    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 2.05/0.69    inference(cnf_transformation,[],[f42])).
% 2.05/0.69  fof(f42,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.05/0.69    inference(flattening,[],[f41])).
% 2.05/0.69  fof(f41,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.05/0.69    inference(ennf_transformation,[],[f5])).
% 2.05/0.69  fof(f5,axiom,(
% 2.05/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.05/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 2.05/0.69  fof(f243,plain,(
% 2.05/0.69    ( ! [X7] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X7,sK1) | k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X7) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X7))) )),
% 2.05/0.69    inference(resolution,[],[f100,f79])).
% 2.05/0.69  fof(f79,plain,(
% 2.05/0.69    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 2.05/0.69    inference(cnf_transformation,[],[f46])).
% 2.05/0.69  fof(f46,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.69    inference(flattening,[],[f45])).
% 2.05/0.69  fof(f45,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.69    inference(ennf_transformation,[],[f8])).
% 2.05/0.69  fof(f8,axiom,(
% 2.05/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.05/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 2.05/0.69  fof(f100,plain,(
% 2.05/0.69    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.05/0.69    inference(subsumption_resolution,[],[f99,f58])).
% 2.05/0.69  fof(f99,plain,(
% 2.05/0.69    v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.05/0.69    inference(subsumption_resolution,[],[f98,f60])).
% 2.05/0.69  fof(f98,plain,(
% 2.05/0.69    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.05/0.69    inference(subsumption_resolution,[],[f88,f59])).
% 2.05/0.69  fof(f88,plain,(
% 2.05/0.69    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.05/0.69    inference(resolution,[],[f57,f68])).
% 2.05/0.69  fof(f68,plain,(
% 2.05/0.69    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))) )),
% 2.05/0.69    inference(cnf_transformation,[],[f29])).
% 2.05/0.69  fof(f2033,plain,(
% 2.05/0.69    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) = k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(resolution,[],[f728,f190])).
% 2.05/0.69  fof(f728,plain,(
% 2.05/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f727,f58])).
% 2.05/0.69  fof(f727,plain,(
% 2.05/0.69    ( ! [X0] : (v2_struct_0(sK0) | ~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f726,f59])).
% 2.05/0.69  fof(f726,plain,(
% 2.05/0.69    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f724,f60])).
% 2.05/0.69  fof(f724,plain,(
% 2.05/0.69    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X0)) = k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1))) )),
% 2.05/0.69    inference(resolution,[],[f308,f57])).
% 2.05/0.69  fof(f308,plain,(
% 2.05/0.69    ( ! [X14,X15] : (~m1_pre_topc(sK1,X14) | ~l1_pre_topc(X14) | ~v2_pre_topc(X14) | v2_struct_0(X14) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f307,f75])).
% 2.05/0.69  fof(f75,plain,(
% 2.05/0.69    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 2.05/0.69    inference(cnf_transformation,[],[f40])).
% 2.05/0.69  fof(f40,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.05/0.69    inference(flattening,[],[f39])).
% 2.05/0.69  fof(f39,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.05/0.69    inference(ennf_transformation,[],[f15])).
% 2.05/0.69  fof(f15,axiom,(
% 2.05/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.05/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 2.05/0.69  fof(f307,plain,(
% 2.05/0.69    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | v2_struct_0(X14) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f306,f103])).
% 2.05/0.69  fof(f306,plain,(
% 2.05/0.69    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f305,f97])).
% 2.05/0.69  fof(f305,plain,(
% 2.05/0.69    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f304,f60])).
% 2.05/0.69  fof(f304,plain,(
% 2.05/0.69    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f303,f59])).
% 2.05/0.69  fof(f303,plain,(
% 2.05/0.69    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f247,f58])).
% 2.05/0.69  fof(f247,plain,(
% 2.05/0.69    ( ! [X14,X15] : (~v2_pre_topc(X14) | ~l1_pre_topc(X14) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X14) | ~m1_pre_topc(X15,X14) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X14) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X15,sK1) | k3_tmap_1(X14,sK0,sK1,X15,k4_tmap_1(sK0,sK1)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X15))) )),
% 2.05/0.69    inference(resolution,[],[f100,f83])).
% 2.05/0.69  fof(f83,plain,(
% 2.05/0.69    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 2.05/0.69    inference(cnf_transformation,[],[f50])).
% 2.05/0.69  fof(f50,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.69    inference(flattening,[],[f49])).
% 2.05/0.69  fof(f49,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.69    inference(ennf_transformation,[],[f9])).
% 2.05/0.69  fof(f9,axiom,(
% 2.05/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 2.05/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 2.05/0.69  fof(f2011,plain,(
% 2.05/0.69    m1_subset_1(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.05/0.69    inference(resolution,[],[f588,f57])).
% 2.05/0.69  fof(f588,plain,(
% 2.05/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f587,f58])).
% 2.05/0.69  fof(f587,plain,(
% 2.05/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f586,f59])).
% 2.05/0.69  fof(f586,plain,(
% 2.05/0.69    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f584,f60])).
% 2.05/0.69  fof(f584,plain,(
% 2.05/0.69    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | m1_subset_1(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 2.05/0.69    inference(resolution,[],[f302,f57])).
% 2.05/0.69  fof(f302,plain,(
% 2.05/0.69    ( ! [X12,X13] : (~m1_pre_topc(sK1,X12) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | ~m1_pre_topc(X13,X12) | v2_struct_0(X12) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f301,f103])).
% 2.05/0.69  fof(f301,plain,(
% 2.05/0.69    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f300,f97])).
% 2.05/0.69  fof(f300,plain,(
% 2.05/0.69    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f299,f60])).
% 2.05/0.69  fof(f299,plain,(
% 2.05/0.69    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f298,f59])).
% 2.05/0.69  fof(f298,plain,(
% 2.05/0.69    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f246,f58])).
% 2.05/0.69  fof(f246,plain,(
% 2.05/0.69    ( ! [X12,X13] : (~v2_pre_topc(X12) | ~l1_pre_topc(X12) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X12) | ~m1_pre_topc(X13,X12) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X12) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(k3_tmap_1(X12,sK0,sK1,X13,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK0))))) )),
% 2.05/0.69    inference(resolution,[],[f100,f82])).
% 2.05/0.69  fof(f82,plain,(
% 2.05/0.69    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))) )),
% 2.05/0.69    inference(cnf_transformation,[],[f48])).
% 2.05/0.69  fof(f48,plain,(
% 2.05/0.69    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.69    inference(flattening,[],[f47])).
% 2.05/0.69  fof(f47,plain,(
% 2.05/0.69    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.69    inference(ennf_transformation,[],[f10])).
% 2.05/0.69  fof(f10,axiom,(
% 2.05/0.69    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 2.05/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 2.05/0.69  fof(f2123,plain,(
% 2.05/0.69    ~m1_subset_1(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(forward_demodulation,[],[f2122,f2096])).
% 2.05/0.69  fof(f2122,plain,(
% 2.05/0.69    ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(subsumption_resolution,[],[f2099,f2038])).
% 2.05/0.69  fof(f2038,plain,(
% 2.05/0.69    v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.05/0.69    inference(backward_demodulation,[],[f998,f2034])).
% 2.05/0.69  fof(f998,plain,(
% 2.05/0.69    v1_funct_2(k3_tmap_1(sK0,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.05/0.69    inference(resolution,[],[f545,f57])).
% 2.05/0.69  fof(f545,plain,(
% 2.05/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f544,f58])).
% 2.05/0.69  fof(f544,plain,(
% 2.05/0.69    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f543,f59])).
% 2.05/0.69  fof(f543,plain,(
% 2.05/0.69    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f541,f60])).
% 2.05/0.69  fof(f541,plain,(
% 2.05/0.69    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | v1_funct_2(k3_tmap_1(sK0,sK0,sK1,X0,k4_tmap_1(sK0,sK1)),u1_struct_0(X0),u1_struct_0(sK0))) )),
% 2.05/0.69    inference(resolution,[],[f297,f57])).
% 2.05/0.69  fof(f297,plain,(
% 2.05/0.69    ( ! [X10,X11] : (~m1_pre_topc(sK1,X10) | ~l1_pre_topc(X10) | ~v2_pre_topc(X10) | ~m1_pre_topc(X11,X10) | v2_struct_0(X10) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f296,f103])).
% 2.05/0.69  fof(f296,plain,(
% 2.05/0.69    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f295,f97])).
% 2.05/0.69  fof(f295,plain,(
% 2.05/0.69    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f294,f60])).
% 2.05/0.69  fof(f294,plain,(
% 2.05/0.69    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f293,f59])).
% 2.05/0.69  fof(f293,plain,(
% 2.05/0.69    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f245,f58])).
% 2.05/0.69  fof(f245,plain,(
% 2.05/0.69    ( ! [X10,X11] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X10) | ~m1_pre_topc(X11,X10) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X10) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_2(k3_tmap_1(X10,sK0,sK1,X11,k4_tmap_1(sK0,sK1)),u1_struct_0(X11),u1_struct_0(sK0))) )),
% 2.05/0.69    inference(resolution,[],[f100,f81])).
% 2.05/0.69  fof(f81,plain,(
% 2.05/0.69    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))) )),
% 2.05/0.69    inference(cnf_transformation,[],[f48])).
% 2.05/0.69  fof(f2099,plain,(
% 2.05/0.69    ~v1_funct_2(k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(backward_demodulation,[],[f992,f2096])).
% 2.05/0.69  fof(f992,plain,(
% 2.05/0.69    ~v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(subsumption_resolution,[],[f991,f97])).
% 2.05/0.69  fof(f991,plain,(
% 2.05/0.69    ~v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(subsumption_resolution,[],[f990,f514])).
% 2.05/0.69  fof(f514,plain,(
% 2.05/0.69    v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.05/0.69    inference(resolution,[],[f485,f190])).
% 2.05/0.69  fof(f485,plain,(
% 2.05/0.69    ( ! [X1] : (~m1_pre_topc(X1,sK1) | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f484,f56])).
% 2.05/0.69  fof(f484,plain,(
% 2.05/0.69    ( ! [X1] : (~m1_pre_topc(X1,sK1) | v2_struct_0(sK1) | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f483,f114])).
% 2.05/0.69  fof(f483,plain,(
% 2.05/0.69    ( ! [X1] : (~v2_pre_topc(sK1) | ~m1_pre_topc(X1,sK1) | v2_struct_0(sK1) | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f479,f115])).
% 2.05/0.69  fof(f479,plain,(
% 2.05/0.69    ( ! [X1] : (~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~m1_pre_topc(X1,sK1) | v2_struct_0(sK1) | v1_funct_1(k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(resolution,[],[f292,f190])).
% 2.05/0.69  fof(f292,plain,(
% 2.05/0.69    ( ! [X8,X9] : (~m1_pre_topc(sK1,X8) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | ~m1_pre_topc(X9,X8) | v2_struct_0(X8) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f291,f103])).
% 2.05/0.69  fof(f291,plain,(
% 2.05/0.69    ( ! [X8,X9] : (~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~m1_pre_topc(sK1,X8) | ~m1_pre_topc(X9,X8) | v2_struct_0(X8) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f290,f97])).
% 2.05/0.69  fof(f290,plain,(
% 2.05/0.69    ( ! [X8,X9] : (~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~m1_pre_topc(sK1,X8) | ~m1_pre_topc(X9,X8) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X8) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f289,f60])).
% 2.05/0.69  fof(f289,plain,(
% 2.05/0.69    ( ! [X8,X9] : (~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X8) | ~m1_pre_topc(X9,X8) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X8) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f288,f59])).
% 2.05/0.69  fof(f288,plain,(
% 2.05/0.69    ( ! [X8,X9] : (~v2_pre_topc(X8) | ~l1_pre_topc(X8) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X8) | ~m1_pre_topc(X9,X8) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X8) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f244,f58])).
% 2.05/0.69  fof(f244,plain,(
% 2.05/0.69    ( ! [X8,X9] : (~v2_pre_topc(X8) | ~l1_pre_topc(X8) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,X8) | ~m1_pre_topc(X9,X8) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X8) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_funct_1(k3_tmap_1(X8,sK0,sK1,X9,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(resolution,[],[f100,f80])).
% 2.05/0.69  fof(f80,plain,(
% 2.05/0.69    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | v2_struct_0(X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) )),
% 2.05/0.69    inference(cnf_transformation,[],[f48])).
% 2.05/0.69  fof(f990,plain,(
% 2.05/0.69    ~v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(subsumption_resolution,[],[f989,f103])).
% 2.05/0.69  fof(f989,plain,(
% 2.05/0.69    ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(subsumption_resolution,[],[f988,f100])).
% 2.05/0.69  fof(f988,plain,(
% 2.05/0.69    ~v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))) | ~v1_funct_2(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k4_tmap_1(sK0,sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(resolution,[],[f540,f62])).
% 2.05/0.69  fof(f62,plain,(
% 2.05/0.69    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~v1_funct_1(X2)) )),
% 2.05/0.69    inference(cnf_transformation,[],[f23])).
% 2.05/0.69  fof(f23,plain,(
% 2.05/0.69    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.05/0.69    inference(flattening,[],[f22])).
% 2.05/0.69  fof(f22,plain,(
% 2.05/0.69    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.05/0.69    inference(ennf_transformation,[],[f4])).
% 2.05/0.69  fof(f4,axiom,(
% 2.05/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.05/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.05/0.69  fof(f540,plain,(
% 2.05/0.69    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.05/0.69    inference(subsumption_resolution,[],[f539,f56])).
% 2.05/0.69  fof(f539,plain,(
% 2.05/0.69    v2_struct_0(sK1) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.05/0.69    inference(subsumption_resolution,[],[f538,f114])).
% 2.05/0.69  fof(f538,plain,(
% 2.05/0.69    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.05/0.69    inference(subsumption_resolution,[],[f534,f115])).
% 2.05/0.69  fof(f534,plain,(
% 2.05/0.69    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))),
% 2.05/0.69    inference(resolution,[],[f279,f190])).
% 2.05/0.69  fof(f279,plain,(
% 2.05/0.69    ( ! [X6] : (~m1_pre_topc(sK1,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f278,f103])).
% 2.05/0.69  fof(f278,plain,(
% 2.05/0.69    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK1,X6) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f277,f97])).
% 2.05/0.69  fof(f277,plain,(
% 2.05/0.69    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f276,f56])).
% 2.05/0.69  fof(f276,plain,(
% 2.05/0.69    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f275,f60])).
% 2.05/0.69  fof(f275,plain,(
% 2.05/0.69    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f274,f59])).
% 2.05/0.69  fof(f274,plain,(
% 2.05/0.69    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f242,f58])).
% 2.05/0.69  fof(f242,plain,(
% 2.05/0.69    ( ! [X6] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X6) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(X6) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k3_tmap_1(X6,sK0,sK1,sK1,k4_tmap_1(sK0,sK1)))) )),
% 2.05/0.69    inference(resolution,[],[f100,f66])).
% 2.05/0.69  fof(f66,plain,(
% 2.05/0.69    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))) )),
% 2.05/0.69    inference(cnf_transformation,[],[f27])).
% 2.05/0.69  fof(f27,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.69    inference(flattening,[],[f26])).
% 2.05/0.69  fof(f26,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.69    inference(ennf_transformation,[],[f14])).
% 2.05/0.69  fof(f14,axiom,(
% 2.05/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 2.05/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).
% 2.05/0.69  fof(f2096,plain,(
% 2.05/0.69    k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(forward_demodulation,[],[f2095,f477])).
% 2.05/0.69  fof(f2095,plain,(
% 2.05/0.69    k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(sK1)) = k3_tmap_1(sK1,sK0,sK1,sK1,k4_tmap_1(sK0,sK1))),
% 2.05/0.69    inference(resolution,[],[f731,f190])).
% 2.05/0.69  fof(f731,plain,(
% 2.05/0.69    ( ! [X1] : (~m1_pre_topc(X1,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f730,f56])).
% 2.05/0.69  fof(f730,plain,(
% 2.05/0.69    ( ! [X1] : (v2_struct_0(sK1) | ~m1_pre_topc(X1,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f729,f114])).
% 2.05/0.69  fof(f729,plain,(
% 2.05/0.69    ( ! [X1] : (~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(X1,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f725,f115])).
% 2.05/0.69  fof(f725,plain,(
% 2.05/0.69    ( ! [X1] : (~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(X1,sK1) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),u1_struct_0(X1)) = k3_tmap_1(sK1,sK0,sK1,X1,k4_tmap_1(sK0,sK1))) )),
% 2.05/0.69    inference(resolution,[],[f308,f190])).
% 2.05/0.69  fof(f903,plain,(
% 2.05/0.69    r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.05/0.69    inference(subsumption_resolution,[],[f902,f54])).
% 2.05/0.69  fof(f54,plain,(
% 2.05/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.05/0.69    inference(cnf_transformation,[],[f21])).
% 2.05/0.69  fof(f902,plain,(
% 2.05/0.69    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.05/0.69    inference(subsumption_resolution,[],[f901,f56])).
% 2.05/0.69  fof(f901,plain,(
% 2.05/0.69    v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.05/0.69    inference(subsumption_resolution,[],[f900,f52])).
% 2.05/0.69  fof(f52,plain,(
% 2.05/0.69    v1_funct_1(sK2)),
% 2.05/0.69    inference(cnf_transformation,[],[f21])).
% 2.05/0.69  fof(f900,plain,(
% 2.05/0.69    ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.05/0.69    inference(subsumption_resolution,[],[f894,f190])).
% 2.05/0.69  fof(f894,plain,(
% 2.05/0.69    ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.05/0.69    inference(resolution,[],[f265,f53])).
% 2.05/0.69  fof(f53,plain,(
% 2.05/0.69    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.05/0.69    inference(cnf_transformation,[],[f21])).
% 2.05/0.69  fof(f265,plain,(
% 2.05/0.69    ( ! [X2,X3] : (~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(X3) | v2_struct_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f264,f103])).
% 2.05/0.69  fof(f264,plain,(
% 2.05/0.69    ( ! [X2,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f263,f58])).
% 2.05/0.69  fof(f263,plain,(
% 2.05/0.69    ( ! [X2,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f262,f97])).
% 2.05/0.69  fof(f262,plain,(
% 2.05/0.69    ( ! [X2,X3] : (v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f261,f115])).
% 2.05/0.69  fof(f261,plain,(
% 2.05/0.69    ( ! [X2,X3] : (~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f260,f114])).
% 2.05/0.69  fof(f260,plain,(
% 2.05/0.69    ( ! [X2,X3] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f259,f56])).
% 2.05/0.69  fof(f259,plain,(
% 2.05/0.69    ( ! [X2,X3] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f258,f60])).
% 2.05/0.69  fof(f258,plain,(
% 2.05/0.69    ( ! [X2,X3] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f240,f59])).
% 2.05/0.69  fof(f240,plain,(
% 2.05/0.69    ( ! [X2,X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | r2_hidden(sK3(sK0,sK1,X2,k4_tmap_1(sK0,sK1),X3),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X2),X3)) )),
% 2.05/0.69    inference(resolution,[],[f100,f64])).
% 2.05/0.69  fof(f64,plain,(
% 2.05/0.69    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | r2_hidden(sK3(X0,X1,X2,X3,X4),u1_struct_0(X2)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 2.05/0.69    inference(cnf_transformation,[],[f25])).
% 2.05/0.69  fof(f25,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.69    inference(flattening,[],[f24])).
% 2.05/0.69  fof(f24,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.69    inference(ennf_transformation,[],[f13])).
% 2.05/0.69  fof(f13,axiom,(
% 2.05/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 2.05/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).
% 2.05/0.69  fof(f2616,plain,(
% 2.05/0.69    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | v1_xboole_0(u1_struct_0(sK1))),
% 2.05/0.69    inference(backward_demodulation,[],[f2292,f2615])).
% 2.05/0.69  fof(f2615,plain,(
% 2.05/0.69    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.05/0.69    inference(subsumption_resolution,[],[f2612,f2162])).
% 2.05/0.69  fof(f2612,plain,(
% 2.05/0.69    ~r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.05/0.69    inference(resolution,[],[f2295,f107])).
% 2.05/0.69  fof(f107,plain,(
% 2.05/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f106,f58])).
% 2.05/0.69  fof(f106,plain,(
% 2.05/0.69    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f105,f56])).
% 2.05/0.69  fof(f105,plain,(
% 2.05/0.69    ( ! [X0] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f104,f60])).
% 2.05/0.69  fof(f104,plain,(
% 2.05/0.69    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f90,f59])).
% 2.05/0.69  fof(f90,plain,(
% 2.05/0.69    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.05/0.69    inference(resolution,[],[f57,f70])).
% 2.05/0.69  fof(f70,plain,(
% 2.05/0.69    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2) )),
% 2.05/0.69    inference(cnf_transformation,[],[f31])).
% 2.05/0.69  fof(f31,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.69    inference(flattening,[],[f30])).
% 2.05/0.69  fof(f30,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.69    inference(ennf_transformation,[],[f16])).
% 2.05/0.69  fof(f16,axiom,(
% 2.05/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 2.05/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).
% 2.05/0.69  fof(f2295,plain,(
% 2.05/0.69    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))),
% 2.05/0.69    inference(resolution,[],[f2161,f110])).
% 2.05/0.69  fof(f110,plain,(
% 2.05/0.69    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f109,f58])).
% 2.05/0.69  fof(f109,plain,(
% 2.05/0.69    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f108,f56])).
% 2.05/0.69  fof(f108,plain,(
% 2.05/0.69    ( ! [X1] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f91,f60])).
% 2.05/0.69  fof(f91,plain,(
% 2.05/0.69    ( ! [X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.05/0.69    inference(resolution,[],[f57,f74])).
% 2.05/0.69  fof(f74,plain,(
% 2.05/0.69    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 2.05/0.69    inference(cnf_transformation,[],[f38])).
% 2.05/0.69  fof(f38,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.69    inference(flattening,[],[f37])).
% 2.05/0.69  fof(f37,plain,(
% 2.05/0.69    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.69    inference(ennf_transformation,[],[f7])).
% 2.05/0.69  fof(f7,axiom,(
% 2.05/0.69    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.05/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 2.05/0.69  fof(f2161,plain,(
% 2.05/0.69    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.05/0.69    inference(subsumption_resolution,[],[f2127,f55])).
% 2.05/0.69  fof(f2127,plain,(
% 2.05/0.69    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1))),
% 2.05/0.69    inference(backward_demodulation,[],[f875,f2125])).
% 2.05/0.69  fof(f875,plain,(
% 2.05/0.69    m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.05/0.69    inference(subsumption_resolution,[],[f874,f54])).
% 2.05/0.69  fof(f874,plain,(
% 2.05/0.69    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.05/0.69    inference(subsumption_resolution,[],[f873,f56])).
% 2.05/0.69  fof(f873,plain,(
% 2.05/0.69    v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.05/0.69    inference(subsumption_resolution,[],[f872,f52])).
% 2.05/0.69  fof(f872,plain,(
% 2.05/0.69    ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.05/0.69    inference(subsumption_resolution,[],[f866,f190])).
% 2.05/0.69  fof(f866,plain,(
% 2.05/0.69    ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.05/0.69    inference(resolution,[],[f257,f53])).
% 2.05/0.69  fof(f257,plain,(
% 2.05/0.69    ( ! [X0,X1] : (~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(X1) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f256,f103])).
% 2.05/0.69  fof(f256,plain,(
% 2.05/0.69    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f255,f58])).
% 2.05/0.69  fof(f255,plain,(
% 2.05/0.69    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f254,f97])).
% 2.05/0.69  fof(f254,plain,(
% 2.05/0.69    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f253,f115])).
% 2.05/0.69  fof(f253,plain,(
% 2.05/0.69    ( ! [X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f252,f114])).
% 2.05/0.69  fof(f252,plain,(
% 2.05/0.69    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f251,f56])).
% 2.05/0.69  fof(f251,plain,(
% 2.05/0.69    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f250,f60])).
% 2.05/0.69  fof(f250,plain,(
% 2.05/0.69    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f239,f59])).
% 2.05/0.69  fof(f239,plain,(
% 2.05/0.69    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) | m1_subset_1(sK3(sK0,sK1,X0,k4_tmap_1(sK0,sK1),X1),u1_struct_0(sK1)) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X0),X1)) )),
% 2.05/0.69    inference(resolution,[],[f100,f63])).
% 2.05/0.69  fof(f63,plain,(
% 2.05/0.69    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | m1_subset_1(sK3(X0,X1,X2,X3,X4),u1_struct_0(X1)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 2.05/0.69    inference(cnf_transformation,[],[f25])).
% 2.05/0.69  fof(f2292,plain,(
% 2.05/0.69    v1_xboole_0(u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.05/0.69    inference(resolution,[],[f2161,f310])).
% 2.05/0.69  fof(f310,plain,(
% 2.05/0.69    ( ! [X16] : (~m1_subset_1(X16,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f309,f103])).
% 2.05/0.69  fof(f309,plain,(
% 2.05/0.69    ( ! [X16] : (v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X16,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f248,f97])).
% 2.05/0.69  fof(f248,plain,(
% 2.05/0.69    ( ! [X16] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X16,u1_struct_0(sK1)) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X16) = k1_funct_1(k4_tmap_1(sK0,sK1),X16)) )),
% 2.05/0.69    inference(resolution,[],[f100,f71])).
% 2.05/0.69  fof(f71,plain,(
% 2.05/0.69    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 2.05/0.69    inference(cnf_transformation,[],[f33])).
% 2.05/0.69  fof(f33,plain,(
% 2.05/0.69    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.05/0.69    inference(flattening,[],[f32])).
% 2.05/0.69  fof(f32,plain,(
% 2.05/0.69    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.05/0.69    inference(ennf_transformation,[],[f3])).
% 2.05/0.69  fof(f3,axiom,(
% 2.05/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 2.05/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 2.05/0.69  fof(f2163,plain,(
% 2.05/0.69    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.05/0.69    inference(subsumption_resolution,[],[f2131,f55])).
% 2.05/0.69  fof(f2131,plain,(
% 2.05/0.69    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.05/0.69    inference(backward_demodulation,[],[f1213,f2125])).
% 2.05/0.69  fof(f1213,plain,(
% 2.05/0.69    k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.05/0.69    inference(subsumption_resolution,[],[f1212,f54])).
% 2.05/0.69  fof(f1212,plain,(
% 2.05/0.69    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.05/0.69    inference(subsumption_resolution,[],[f1211,f56])).
% 2.05/0.69  fof(f1211,plain,(
% 2.05/0.69    v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.05/0.69    inference(subsumption_resolution,[],[f1210,f52])).
% 2.05/0.69  fof(f1210,plain,(
% 2.05/0.69    ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.05/0.69    inference(subsumption_resolution,[],[f1202,f190])).
% 2.05/0.69  fof(f1202,plain,(
% 2.05/0.69    ~m1_pre_topc(sK1,sK1) | ~v1_funct_1(sK2) | v2_struct_0(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),sK1),sK2)),
% 2.05/0.69    inference(resolution,[],[f273,f53])).
% 2.05/0.69  fof(f273,plain,(
% 2.05/0.69    ( ! [X4,X5] : (~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(X5) | v2_struct_0(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f272,f103])).
% 2.05/0.69  fof(f272,plain,(
% 2.05/0.69    ( ! [X4,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f271,f58])).
% 2.05/0.69  fof(f271,plain,(
% 2.05/0.69    ( ! [X4,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f270,f97])).
% 2.05/0.69  fof(f270,plain,(
% 2.05/0.69    ( ! [X4,X5] : (v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f269,f115])).
% 2.05/0.69  fof(f269,plain,(
% 2.05/0.69    ( ! [X4,X5] : (~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f268,f114])).
% 2.05/0.69  fof(f268,plain,(
% 2.05/0.69    ( ! [X4,X5] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f267,f56])).
% 2.05/0.69  fof(f267,plain,(
% 2.05/0.69    ( ! [X4,X5] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f266,f60])).
% 2.05/0.69  fof(f266,plain,(
% 2.05/0.69    ( ! [X4,X5] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.05/0.69    inference(subsumption_resolution,[],[f241,f59])).
% 2.05/0.69  fof(f241,plain,(
% 2.05/0.69    ( ! [X4,X5] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0)))) | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) != k1_funct_1(X5,sK3(sK0,sK1,X4,k4_tmap_1(sK0,sK1),X5)) | r2_funct_2(u1_struct_0(X4),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,k4_tmap_1(sK0,sK1),X4),X5)) )),
% 2.05/0.69    inference(resolution,[],[f100,f65])).
% 2.05/0.69  fof(f65,plain,(
% 2.05/0.69    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X1) | ~v1_funct_1(X3) | v2_struct_0(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK3(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK3(X0,X1,X2,X3,X4)) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)) )),
% 2.05/0.69    inference(cnf_transformation,[],[f25])).
% 2.05/0.69  fof(f2619,plain,(
% 2.05/0.69    sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.05/0.69    inference(subsumption_resolution,[],[f2613,f2162])).
% 2.05/0.69  fof(f2613,plain,(
% 2.05/0.69    ~r2_hidden(sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK1)) | sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK1,k4_tmap_1(sK0,sK1),sK2))),
% 2.05/0.69    inference(resolution,[],[f2295,f51])).
% 2.05/0.69  fof(f51,plain,(
% 2.05/0.69    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3) )),
% 2.05/0.69    inference(cnf_transformation,[],[f21])).
% 2.05/0.69  % SZS output end Proof for theBenchmark
% 2.05/0.69  % (6899)------------------------------
% 2.05/0.69  % (6899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.69  % (6899)Termination reason: Refutation
% 2.05/0.69  
% 2.05/0.69  % (6899)Memory used [KB]: 7547
% 2.05/0.69  % (6899)Time elapsed: 0.252 s
% 2.05/0.69  % (6899)------------------------------
% 2.05/0.69  % (6899)------------------------------
% 2.05/0.69  % (6893)Success in time 0.33 s
%------------------------------------------------------------------------------
