%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:40 EST 2020

% Result     : Theorem 2.35s
% Output     : Refutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :  212 (15870 expanded)
%              Number of leaves         :   15 (2849 expanded)
%              Depth                    :   42
%              Number of atoms          :  910 (106695 expanded)
%              Number of equality atoms :   96 (4531 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5926,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5925,f64])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) ) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) ) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
                & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1))
              & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_tmap_1)).

fof(f5925,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f5924,f5832])).

fof(f5832,plain,(
    ~ v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f339,f5830])).

fof(f5830,plain,(
    ~ v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4953,f5829])).

fof(f5829,plain,(
    v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f5828,f4981])).

fof(f4981,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(resolution,[],[f4951,f386])).

fof(f386,plain,
    ( ~ v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1))
    | v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f385,f361])).

fof(f361,plain,(
    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f360,f308])).

fof(f308,plain,(
    k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f307,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f307,plain,
    ( v2_struct_0(sK0)
    | k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f306,f64])).

fof(f306,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f292,f63])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f292,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(resolution,[],[f127,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f127,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f126,f64])).

fof(f126,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f67,f61])).

fof(f61,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f360,plain,(
    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f359,f62])).

fof(f359,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f358,f64])).

fof(f358,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f302,f63])).

fof(f302,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f127,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_1(k7_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f385,plain,
    ( ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1))
    | v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(forward_demodulation,[],[f384,f308])).

fof(f384,plain,
    ( ~ v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(forward_demodulation,[],[f383,f308])).

fof(f383,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f382,f62])).

fof(f382,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f381,f127])).

fof(f381,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f380,f64])).

fof(f380,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f379,f63])).

fof(f379,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(superposition,[],[f122,f198])).

fof(f198,plain,(
    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f197,f62])).

fof(f197,plain,
    ( v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f196,f64])).

fof(f196,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f193,f63])).

fof(f193,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(resolution,[],[f120,f61])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f119,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
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
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f119,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f118,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f114,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f110,f67])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X3
      | k6_tmap_1(X0,X3) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | v2_struct_0(X0)
      | v3_pre_topc(X1,X0) ) ),
    inference(subsumption_resolution,[],[f121,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f121,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | v3_pre_topc(X1,X0) ) ),
    inference(subsumption_resolution,[],[f89,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).

fof(f4951,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1))
    | v1_tsep_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f58,f4949])).

fof(f4949,plain,(
    k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4948,f2966])).

fof(f2966,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2965,f748])).

fof(f748,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f747,f349])).

fof(f349,plain,(
    ~ v2_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f348,f198])).

fof(f348,plain,(
    ~ v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f347,f62])).

fof(f347,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f346,f64])).

fof(f346,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f299,f63])).

fof(f299,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f127,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(f747,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f717,f291])).

fof(f291,plain,(
    l1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f159,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f159,plain,(
    l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f158,f62])).

fof(f158,plain,
    ( v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f157,f64])).

fof(f157,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f155,f63])).

fof(f155,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f95,f61])).

fof(f717,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(k8_tmap_1(sK0,sK1))
    | v2_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f73,f313])).

fof(f313,plain,(
    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f312,f198])).

fof(f312,plain,(
    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f311,f62])).

fof(f311,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f310,f64])).

fof(f310,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f293,f63])).

fof(f293,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f127,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f2965,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2964,f367])).

fof(f367,plain,(
    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f366,f308])).

fof(f366,plain,(
    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f365,f313])).

fof(f365,plain,(
    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f364,f198])).

fof(f364,plain,(
    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f363,f62])).

fof(f363,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f362,f64])).

fof(f362,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f303,f63])).

fof(f303,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))) ),
    inference(resolution,[],[f127,f100])).

fof(f2964,plain,
    ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2951,f361])).

fof(f2951,plain,
    ( ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f961,f373])).

fof(f373,plain,(
    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f372,f308])).

fof(f372,plain,(
    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f371,f313])).

fof(f371,plain,(
    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f370,f198])).

fof(f370,plain,(
    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) ),
    inference(subsumption_resolution,[],[f369,f62])).

fof(f369,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) ),
    inference(subsumption_resolution,[],[f368,f64])).

fof(f368,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) ),
    inference(subsumption_resolution,[],[f304,f63])).

fof(f304,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) ),
    inference(resolution,[],[f127,f101])).

fof(f961,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X2,X0)
      | v1_xboole_0(X0)
      | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X2,X0,k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f960,f748])).

fof(f960,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X2,X0,k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f959,f367])).

fof(f959,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X2,X0,k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f958,f361])).

fof(f958,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X2,X0,k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f373,f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

fof(f4948,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f4947,f313])).

fof(f4947,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f4946,f198])).

fof(f4946,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f4945,f308])).

fof(f4945,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4944,f373])).

fof(f4944,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4943,f367])).

fof(f4943,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4942,f361])).

fof(f4942,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f4939])).

fof(f4939,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(superposition,[],[f738,f3025])).

fof(f3025,plain,
    ( u1_struct_0(sK1) = sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f3024,f367])).

fof(f3024,plain,
    ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | u1_struct_0(sK1) = sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f3017,f361])).

fof(f3017,plain,
    ( ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | u1_struct_0(sK1) = sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(resolution,[],[f746,f373])).

fof(f746,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
      | u1_struct_0(sK1) = sK4(sK0,sK1,X2)
      | k9_tmap_1(sK0,sK1) = X2 ) ),
    inference(subsumption_resolution,[],[f745,f62])).

fof(f745,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | u1_struct_0(sK1) = sK4(sK0,sK1,X2)
      | k9_tmap_1(sK0,sK1) = X2 ) ),
    inference(subsumption_resolution,[],[f744,f61])).

fof(f744,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | u1_struct_0(sK1) = sK4(sK0,sK1,X2)
      | k9_tmap_1(sK0,sK1) = X2 ) ),
    inference(subsumption_resolution,[],[f743,f64])).

fof(f743,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | u1_struct_0(sK1) = sK4(sK0,sK1,X2)
      | k9_tmap_1(sK0,sK1) = X2 ) ),
    inference(subsumption_resolution,[],[f716,f63])).

fof(f716,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | u1_struct_0(sK1) = sK4(sK0,sK1,X2)
      | k9_tmap_1(sK0,sK1) = X2 ) ),
    inference(superposition,[],[f76,f313])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | v2_struct_0(X0)
      | u1_struct_0(X1) = sK4(X0,X1,X2)
      | k9_tmap_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
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
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).

fof(f738,plain,(
    ! [X0] :
      ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X0))),X0,k7_tmap_1(sK0,sK4(sK0,sK1,X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | k9_tmap_1(sK0,sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f737,f62])).

fof(f737,plain,(
    ! [X0] :
      ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X0))),X0,k7_tmap_1(sK0,sK4(sK0,sK1,X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | v2_struct_0(sK0)
      | k9_tmap_1(sK0,sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f736,f61])).

fof(f736,plain,(
    ! [X0] :
      ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X0))),X0,k7_tmap_1(sK0,sK4(sK0,sK1,X0)))
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | v2_struct_0(sK0)
      | k9_tmap_1(sK0,sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f735,f64])).

fof(f735,plain,(
    ! [X0] :
      ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X0))),X0,k7_tmap_1(sK0,sK4(sK0,sK1,X0)))
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | v2_struct_0(sK0)
      | k9_tmap_1(sK0,sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f714,f63])).

fof(f714,plain,(
    ! [X0] :
      ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X0))),X0,k7_tmap_1(sK0,sK4(sK0,sK1,X0)))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | v2_struct_0(sK0)
      | k9_tmap_1(sK0,sK1) = X0 ) ),
    inference(superposition,[],[f77,f313])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | v2_struct_0(X0)
      | k9_tmap_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,
    ( v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f5828,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f5827,f64])).

fof(f5827,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f5826,f61])).

fof(f5826,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(superposition,[],[f71,f4984])).

fof(f4984,plain,(
    u1_struct_0(sK1) = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f4983,f165])).

fof(f165,plain,
    ( v1_tsep_1(sK1,sK0)
    | u1_struct_0(sK1) = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f163,f64])).

fof(f163,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK1) = sK2(sK0,sK1)
    | v1_tsep_1(sK1,sK0) ),
    inference(resolution,[],[f70,f61])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

fof(f4983,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | u1_struct_0(sK1) = sK2(sK0,sK1) ),
    inference(resolution,[],[f4953,f1033])).

fof(f1033,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1))
    | u1_struct_0(sK1) = sK2(sK0,sK1) ),
    inference(resolution,[],[f339,f389])).

fof(f389,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | u1_struct_0(sK1) = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f388,f64])).

fof(f388,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f387,f61])).

fof(f387,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f165,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f106,f67])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK2(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4953,plain,
    ( ~ v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f225,f4949])).

fof(f225,plain,
    ( ~ v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f211,f224])).

fof(f224,plain,(
    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f223,f62])).

fof(f223,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f222,f64])).

fof(f222,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f219,f63])).

fof(f219,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    inference(resolution,[],[f92,f61])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).

fof(f211,plain,
    ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f132,f210])).

fof(f210,plain,(
    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f209,f62])).

fof(f209,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f208,f64])).

fof(f208,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f205,f63])).

fof(f205,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f91,f61])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f132,plain,
    ( ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f111,f131])).

fof(f131,plain,(
    v1_funct_1(k9_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f130,f62])).

fof(f130,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k9_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f129,f64])).

fof(f129,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k9_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f128,f63])).

fof(f128,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k9_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f90,f61])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_1(k9_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f111,plain,
    ( ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f60,f61])).

fof(f60,plain,
    ( ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f339,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f338,f308])).

fof(f338,plain,
    ( v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(forward_demodulation,[],[f337,f198])).

fof(f337,plain,
    ( v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f336,f62])).

fof(f336,plain,
    ( v2_struct_0(sK0)
    | v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f335,f64])).

fof(f335,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f297,f63])).

fof(f297,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(resolution,[],[f127,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5924,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f5923,f61])).

fof(f5923,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f5829,f112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (30990)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (30998)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (31001)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.47  % (30989)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (30997)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (30987)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (30996)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (30988)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (30985)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (30999)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (30985)Refutation not found, incomplete strategy% (30985)------------------------------
% 0.20/0.50  % (30985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (30985)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (30985)Memory used [KB]: 10618
% 0.20/0.50  % (30985)Time elapsed: 0.090 s
% 0.20/0.50  % (30985)------------------------------
% 0.20/0.50  % (30985)------------------------------
% 0.20/0.51  % (30994)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (31000)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (30984)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (30986)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (31003)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (30992)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.52  % (30991)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.52  % (30995)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.52  % (30993)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.52  % (31004)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.52  % (31004)Refutation not found, incomplete strategy% (31004)------------------------------
% 0.20/0.52  % (31004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31004)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (31004)Memory used [KB]: 10618
% 0.20/0.52  % (31004)Time elapsed: 0.116 s
% 0.20/0.52  % (31004)------------------------------
% 0.20/0.52  % (31004)------------------------------
% 0.20/0.52  % (31002)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.54/0.56  % (30994)Refutation not found, incomplete strategy% (30994)------------------------------
% 1.54/0.56  % (30994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (30994)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (30994)Memory used [KB]: 6524
% 1.54/0.56  % (30994)Time elapsed: 0.142 s
% 1.54/0.56  % (30994)------------------------------
% 1.54/0.56  % (30994)------------------------------
% 2.35/0.69  % (31001)Refutation found. Thanks to Tanya!
% 2.35/0.69  % SZS status Theorem for theBenchmark
% 2.35/0.70  % SZS output start Proof for theBenchmark
% 2.35/0.70  fof(f5926,plain,(
% 2.35/0.70    $false),
% 2.35/0.70    inference(subsumption_resolution,[],[f5925,f64])).
% 2.35/0.70  fof(f64,plain,(
% 2.35/0.70    l1_pre_topc(sK0)),
% 2.35/0.70    inference(cnf_transformation,[],[f21])).
% 2.35/0.70  fof(f21,plain,(
% 2.35/0.70    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.35/0.70    inference(flattening,[],[f20])).
% 2.35/0.70  fof(f20,plain,(
% 2.35/0.70    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1)))) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.35/0.70    inference(ennf_transformation,[],[f19])).
% 2.35/0.70  fof(f19,negated_conjecture,(
% 2.35/0.70    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 2.35/0.70    inference(negated_conjecture,[],[f18])).
% 2.35/0.70  fof(f18,conjecture,(
% 2.35/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k9_tmap_1(X0,X1),X0,k8_tmap_1(X0,X1)) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))))),
% 2.35/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_tmap_1)).
% 2.35/0.70  fof(f5925,plain,(
% 2.35/0.70    ~l1_pre_topc(sK0)),
% 2.35/0.70    inference(subsumption_resolution,[],[f5924,f5832])).
% 2.35/0.70  fof(f5832,plain,(
% 2.35/0.70    ~v3_pre_topc(u1_struct_0(sK1),sK0)),
% 2.35/0.70    inference(subsumption_resolution,[],[f339,f5830])).
% 2.35/0.70  fof(f5830,plain,(
% 2.35/0.70    ~v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1))),
% 2.35/0.70    inference(subsumption_resolution,[],[f4953,f5829])).
% 2.35/0.70  fof(f5829,plain,(
% 2.35/0.70    v1_tsep_1(sK1,sK0)),
% 2.35/0.70    inference(subsumption_resolution,[],[f5828,f4981])).
% 2.35/0.70  fof(f4981,plain,(
% 2.35/0.70    v3_pre_topc(u1_struct_0(sK1),sK0) | v1_tsep_1(sK1,sK0)),
% 2.35/0.70    inference(resolution,[],[f4951,f386])).
% 2.35/0.71  fof(f386,plain,(
% 2.35/0.71    ~v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1)) | v3_pre_topc(u1_struct_0(sK1),sK0)),
% 2.35/0.71    inference(subsumption_resolution,[],[f385,f361])).
% 2.35/0.71  fof(f361,plain,(
% 2.35/0.71    v1_funct_1(k6_partfun1(u1_struct_0(sK0)))),
% 2.35/0.71    inference(forward_demodulation,[],[f360,f308])).
% 2.35/0.71  fof(f308,plain,(
% 2.35/0.71    k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0))),
% 2.35/0.71    inference(subsumption_resolution,[],[f307,f62])).
% 2.35/0.71  fof(f62,plain,(
% 2.35/0.71    ~v2_struct_0(sK0)),
% 2.35/0.71    inference(cnf_transformation,[],[f21])).
% 2.35/0.71  fof(f307,plain,(
% 2.35/0.71    v2_struct_0(sK0) | k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0))),
% 2.35/0.71    inference(subsumption_resolution,[],[f306,f64])).
% 2.35/0.71  fof(f306,plain,(
% 2.35/0.71    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0))),
% 2.35/0.71    inference(subsumption_resolution,[],[f292,f63])).
% 2.35/0.71  fof(f63,plain,(
% 2.35/0.71    v2_pre_topc(sK0)),
% 2.35/0.71    inference(cnf_transformation,[],[f21])).
% 2.35/0.71  fof(f292,plain,(
% 2.35/0.71    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0))),
% 2.35/0.71    inference(resolution,[],[f127,f82])).
% 2.35/0.71  fof(f82,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f35])).
% 2.35/0.71  fof(f35,plain,(
% 2.35/0.71    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.35/0.71    inference(flattening,[],[f34])).
% 2.35/0.71  fof(f34,plain,(
% 2.35/0.71    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.35/0.71    inference(ennf_transformation,[],[f5])).
% 2.35/0.71  fof(f5,axiom,(
% 2.35/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).
% 2.35/0.71  fof(f127,plain,(
% 2.35/0.71    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.35/0.71    inference(subsumption_resolution,[],[f126,f64])).
% 2.35/0.71  fof(f126,plain,(
% 2.35/0.71    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.35/0.71    inference(resolution,[],[f67,f61])).
% 2.35/0.71  fof(f61,plain,(
% 2.35/0.71    m1_pre_topc(sK1,sK0)),
% 2.35/0.71    inference(cnf_transformation,[],[f21])).
% 2.35/0.71  fof(f67,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f24])).
% 2.35/0.71  fof(f24,plain,(
% 2.35/0.71    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.35/0.71    inference(ennf_transformation,[],[f16])).
% 2.35/0.71  fof(f16,axiom,(
% 2.35/0.71    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 2.35/0.71  fof(f360,plain,(
% 2.35/0.71    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 2.35/0.71    inference(subsumption_resolution,[],[f359,f62])).
% 2.35/0.71  fof(f359,plain,(
% 2.35/0.71    v2_struct_0(sK0) | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 2.35/0.71    inference(subsumption_resolution,[],[f358,f64])).
% 2.35/0.71  fof(f358,plain,(
% 2.35/0.71    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 2.35/0.71    inference(subsumption_resolution,[],[f302,f63])).
% 2.35/0.71  fof(f302,plain,(
% 2.35/0.71    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 2.35/0.71    inference(resolution,[],[f127,f99])).
% 2.35/0.71  fof(f99,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_1(k7_tmap_1(X0,X1))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f47])).
% 2.35/0.71  fof(f47,plain,(
% 2.35/0.71    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.35/0.71    inference(flattening,[],[f46])).
% 2.35/0.71  fof(f46,plain,(
% 2.35/0.71    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.35/0.71    inference(ennf_transformation,[],[f10])).
% 2.35/0.71  fof(f10,axiom,(
% 2.35/0.71    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 2.35/0.71  fof(f385,plain,(
% 2.35/0.71    ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1)) | v3_pre_topc(u1_struct_0(sK1),sK0)),
% 2.35/0.71    inference(forward_demodulation,[],[f384,f308])).
% 2.35/0.71  fof(f384,plain,(
% 2.35/0.71    ~v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | v3_pre_topc(u1_struct_0(sK1),sK0)),
% 2.35/0.71    inference(forward_demodulation,[],[f383,f308])).
% 2.35/0.71  fof(f383,plain,(
% 2.35/0.71    ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | v3_pre_topc(u1_struct_0(sK1),sK0)),
% 2.35/0.71    inference(subsumption_resolution,[],[f382,f62])).
% 2.35/0.71  fof(f382,plain,(
% 2.35/0.71    ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | v3_pre_topc(u1_struct_0(sK1),sK0)),
% 2.35/0.71    inference(subsumption_resolution,[],[f381,f127])).
% 2.35/0.71  fof(f381,plain,(
% 2.35/0.71    ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | v3_pre_topc(u1_struct_0(sK1),sK0)),
% 2.35/0.71    inference(subsumption_resolution,[],[f380,f64])).
% 2.35/0.71  fof(f380,plain,(
% 2.35/0.71    ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | v3_pre_topc(u1_struct_0(sK1),sK0)),
% 2.35/0.71    inference(subsumption_resolution,[],[f379,f63])).
% 2.35/0.71  fof(f379,plain,(
% 2.35/0.71    ~v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | v3_pre_topc(u1_struct_0(sK1),sK0)),
% 2.35/0.71    inference(superposition,[],[f122,f198])).
% 2.35/0.71  fof(f198,plain,(
% 2.35/0.71    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 2.35/0.71    inference(subsumption_resolution,[],[f197,f62])).
% 2.35/0.71  fof(f197,plain,(
% 2.35/0.71    v2_struct_0(sK0) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 2.35/0.71    inference(subsumption_resolution,[],[f196,f64])).
% 2.35/0.71  fof(f196,plain,(
% 2.35/0.71    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 2.35/0.71    inference(subsumption_resolution,[],[f193,f63])).
% 2.35/0.71  fof(f193,plain,(
% 2.35/0.71    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 2.35/0.71    inference(resolution,[],[f120,f61])).
% 2.35/0.71  fof(f120,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f119,f93])).
% 2.35/0.71  fof(f93,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_pre_topc(k8_tmap_1(X0,X1))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f43])).
% 2.35/0.71  fof(f43,plain,(
% 2.35/0.71    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.35/0.71    inference(flattening,[],[f42])).
% 2.35/0.71  fof(f42,plain,(
% 2.35/0.71    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.35/0.71    inference(ennf_transformation,[],[f11])).
% 2.35/0.71  fof(f11,axiom,(
% 2.35/0.71    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 2.35/0.71  fof(f119,plain,(
% 2.35/0.71    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f118,f94])).
% 2.35/0.71  fof(f94,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_pre_topc(k8_tmap_1(X0,X1))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f43])).
% 2.35/0.71  fof(f118,plain,(
% 2.35/0.71    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f114,f95])).
% 2.35/0.71  fof(f95,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | l1_pre_topc(k8_tmap_1(X0,X1))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f43])).
% 2.35/0.71  fof(f114,plain,(
% 2.35/0.71    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f110,f67])).
% 2.35/0.71  fof(f110,plain,(
% 2.35/0.71    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) )),
% 2.35/0.71    inference(equality_resolution,[],[f109])).
% 2.35/0.71  fof(f109,plain,(
% 2.35/0.71    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k6_tmap_1(X0,u1_struct_0(X1)) = X2 | k8_tmap_1(X0,X1) != X2) )),
% 2.35/0.71    inference(equality_resolution,[],[f78])).
% 2.35/0.71  fof(f78,plain,(
% 2.35/0.71    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X3 | k6_tmap_1(X0,X3) = X2 | k8_tmap_1(X0,X1) != X2) )),
% 2.35/0.71    inference(cnf_transformation,[],[f33])).
% 2.35/0.71  fof(f33,plain,(
% 2.35/0.71    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.35/0.71    inference(flattening,[],[f32])).
% 2.35/0.71  fof(f32,plain,(
% 2.35/0.71    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.35/0.71    inference(ennf_transformation,[],[f6])).
% 2.35/0.71  fof(f6,axiom,(
% 2.35/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).
% 2.35/0.71  fof(f122,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | v2_struct_0(X0) | v3_pre_topc(X1,X0)) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f121,f100])).
% 2.35/0.71  fof(f100,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f47])).
% 2.35/0.71  fof(f121,plain,(
% 2.35/0.71    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | v3_pre_topc(X1,X0)) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f89,f101])).
% 2.35/0.71  fof(f101,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f47])).
% 2.35/0.71  fof(f89,plain,(
% 2.35/0.71    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | v3_pre_topc(X1,X0)) )),
% 2.35/0.71    inference(cnf_transformation,[],[f39])).
% 2.35/0.71  fof(f39,plain,(
% 2.35/0.71    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.35/0.71    inference(flattening,[],[f38])).
% 2.35/0.71  fof(f38,plain,(
% 2.35/0.71    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.35/0.71    inference(ennf_transformation,[],[f15])).
% 2.35/0.71  fof(f15,axiom,(
% 2.35/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).
% 2.35/0.71  fof(f4951,plain,(
% 2.35/0.71    v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1)) | v1_tsep_1(sK1,sK0)),
% 2.35/0.71    inference(backward_demodulation,[],[f58,f4949])).
% 2.35/0.71  fof(f4949,plain,(
% 2.35/0.71    k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))),
% 2.35/0.71    inference(subsumption_resolution,[],[f4948,f2966])).
% 2.35/0.71  fof(f2966,plain,(
% 2.35/0.71    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))),
% 2.35/0.71    inference(subsumption_resolution,[],[f2965,f748])).
% 2.35/0.71  fof(f748,plain,(
% 2.35/0.71    ~v1_xboole_0(u1_struct_0(sK0))),
% 2.35/0.71    inference(subsumption_resolution,[],[f747,f349])).
% 2.35/0.71  fof(f349,plain,(
% 2.35/0.71    ~v2_struct_0(k8_tmap_1(sK0,sK1))),
% 2.35/0.71    inference(forward_demodulation,[],[f348,f198])).
% 2.35/0.71  fof(f348,plain,(
% 2.35/0.71    ~v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 2.35/0.71    inference(subsumption_resolution,[],[f347,f62])).
% 2.35/0.71  fof(f347,plain,(
% 2.35/0.71    v2_struct_0(sK0) | ~v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 2.35/0.71    inference(subsumption_resolution,[],[f346,f64])).
% 2.35/0.71  fof(f346,plain,(
% 2.35/0.71    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 2.35/0.71    inference(subsumption_resolution,[],[f299,f63])).
% 2.35/0.71  fof(f299,plain,(
% 2.35/0.71    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 2.35/0.71    inference(resolution,[],[f127,f96])).
% 2.35/0.71  fof(f96,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_struct_0(k6_tmap_1(X0,X1))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f45])).
% 2.35/0.71  fof(f45,plain,(
% 2.35/0.71    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.35/0.71    inference(flattening,[],[f44])).
% 2.35/0.71  fof(f44,plain,(
% 2.35/0.71    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.35/0.71    inference(ennf_transformation,[],[f13])).
% 2.35/0.71  fof(f13,axiom,(
% 2.35/0.71    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).
% 2.35/0.71  fof(f747,plain,(
% 2.35/0.71    ~v1_xboole_0(u1_struct_0(sK0)) | v2_struct_0(k8_tmap_1(sK0,sK1))),
% 2.35/0.71    inference(subsumption_resolution,[],[f717,f291])).
% 2.35/0.71  fof(f291,plain,(
% 2.35/0.71    l1_struct_0(k8_tmap_1(sK0,sK1))),
% 2.35/0.71    inference(resolution,[],[f159,f65])).
% 2.35/0.71  fof(f65,plain,(
% 2.35/0.71    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.35/0.71    inference(cnf_transformation,[],[f22])).
% 2.35/0.71  fof(f22,plain,(
% 2.35/0.71    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.35/0.71    inference(ennf_transformation,[],[f1])).
% 2.35/0.71  fof(f1,axiom,(
% 2.35/0.71    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.35/0.71  fof(f159,plain,(
% 2.35/0.71    l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 2.35/0.71    inference(subsumption_resolution,[],[f158,f62])).
% 2.35/0.71  fof(f158,plain,(
% 2.35/0.71    v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 2.35/0.71    inference(subsumption_resolution,[],[f157,f64])).
% 2.35/0.71  fof(f157,plain,(
% 2.35/0.71    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 2.35/0.71    inference(subsumption_resolution,[],[f155,f63])).
% 2.35/0.71  fof(f155,plain,(
% 2.35/0.71    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 2.35/0.71    inference(resolution,[],[f95,f61])).
% 2.35/0.71  fof(f717,plain,(
% 2.35/0.71    ~v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(k8_tmap_1(sK0,sK1)) | v2_struct_0(k8_tmap_1(sK0,sK1))),
% 2.35/0.71    inference(superposition,[],[f73,f313])).
% 2.35/0.71  fof(f313,plain,(
% 2.35/0.71    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 2.35/0.71    inference(forward_demodulation,[],[f312,f198])).
% 2.35/0.71  fof(f312,plain,(
% 2.35/0.71    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 2.35/0.71    inference(subsumption_resolution,[],[f311,f62])).
% 2.35/0.71  fof(f311,plain,(
% 2.35/0.71    v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 2.35/0.71    inference(subsumption_resolution,[],[f310,f64])).
% 2.35/0.71  fof(f310,plain,(
% 2.35/0.71    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 2.35/0.71    inference(subsumption_resolution,[],[f293,f63])).
% 2.35/0.71  fof(f293,plain,(
% 2.35/0.71    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 2.35/0.71    inference(resolution,[],[f127,f83])).
% 2.35/0.71  fof(f83,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f37])).
% 2.35/0.71  fof(f37,plain,(
% 2.35/0.71    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.35/0.71    inference(flattening,[],[f36])).
% 2.35/0.71  fof(f36,plain,(
% 2.35/0.71    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.35/0.71    inference(ennf_transformation,[],[f14])).
% 2.35/0.71  fof(f14,axiom,(
% 2.35/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 2.35/0.71  fof(f73,plain,(
% 2.35/0.71    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.35/0.71    inference(cnf_transformation,[],[f29])).
% 2.35/0.71  fof(f29,plain,(
% 2.35/0.71    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.35/0.71    inference(flattening,[],[f28])).
% 2.35/0.71  fof(f28,plain,(
% 2.35/0.71    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.35/0.71    inference(ennf_transformation,[],[f3])).
% 2.35/0.71  fof(f3,axiom,(
% 2.35/0.71    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 2.35/0.71  fof(f2965,plain,(
% 2.35/0.71    v1_xboole_0(u1_struct_0(sK0)) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))),
% 2.35/0.71    inference(subsumption_resolution,[],[f2964,f367])).
% 2.35/0.71  fof(f367,plain,(
% 2.35/0.71    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 2.35/0.71    inference(forward_demodulation,[],[f366,f308])).
% 2.35/0.71  fof(f366,plain,(
% 2.35/0.71    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 2.35/0.71    inference(forward_demodulation,[],[f365,f313])).
% 2.35/0.71  fof(f365,plain,(
% 2.35/0.71    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))),
% 2.35/0.71    inference(forward_demodulation,[],[f364,f198])).
% 2.35/0.71  fof(f364,plain,(
% 2.35/0.71    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))),
% 2.35/0.71    inference(subsumption_resolution,[],[f363,f62])).
% 2.35/0.71  fof(f363,plain,(
% 2.35/0.71    v2_struct_0(sK0) | v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))),
% 2.35/0.71    inference(subsumption_resolution,[],[f362,f64])).
% 2.35/0.71  fof(f362,plain,(
% 2.35/0.71    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))),
% 2.35/0.71    inference(subsumption_resolution,[],[f303,f63])).
% 2.35/0.71  fof(f303,plain,(
% 2.35/0.71    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))),
% 2.35/0.71    inference(resolution,[],[f127,f100])).
% 2.35/0.71  fof(f2964,plain,(
% 2.35/0.71    ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))),
% 2.35/0.71    inference(subsumption_resolution,[],[f2951,f361])).
% 2.35/0.71  fof(f2951,plain,(
% 2.35/0.71    ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))),
% 2.35/0.71    inference(resolution,[],[f961,f373])).
% 2.35/0.71  fof(f373,plain,(
% 2.35/0.71    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 2.35/0.71    inference(forward_demodulation,[],[f372,f308])).
% 2.35/0.71  fof(f372,plain,(
% 2.35/0.71    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 2.35/0.71    inference(forward_demodulation,[],[f371,f313])).
% 2.35/0.71  fof(f371,plain,(
% 2.35/0.71    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))),
% 2.35/0.71    inference(forward_demodulation,[],[f370,f198])).
% 2.35/0.71  fof(f370,plain,(
% 2.35/0.71    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))),
% 2.35/0.71    inference(subsumption_resolution,[],[f369,f62])).
% 2.35/0.71  fof(f369,plain,(
% 2.35/0.71    v2_struct_0(sK0) | m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))),
% 2.35/0.71    inference(subsumption_resolution,[],[f368,f64])).
% 2.35/0.71  fof(f368,plain,(
% 2.35/0.71    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))),
% 2.35/0.71    inference(subsumption_resolution,[],[f304,f63])).
% 2.35/0.71  fof(f304,plain,(
% 2.35/0.71    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))),
% 2.35/0.71    inference(resolution,[],[f127,f101])).
% 2.35/0.71  fof(f961,plain,(
% 2.35/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X2,X0) | v1_xboole_0(X0) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X2,X0,k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f960,f748])).
% 2.35/0.71  fof(f960,plain,(
% 2.35/0.71    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X2,X0,k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f959,f367])).
% 2.35/0.71  fof(f959,plain,(
% 2.35/0.71    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X2,X0,k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f958,f361])).
% 2.35/0.71  fof(f958,plain,(
% 2.35/0.71    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X2,X0,k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))) )),
% 2.35/0.71    inference(resolution,[],[f373,f105])).
% 2.35/0.71  fof(f105,plain,(
% 2.35/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X1) | v1_xboole_0(X1) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | r1_funct_2(X0,X1,X2,X3,X4,X4)) )),
% 2.35/0.71    inference(cnf_transformation,[],[f51])).
% 2.35/0.71  fof(f51,plain,(
% 2.35/0.71    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.35/0.71    inference(flattening,[],[f50])).
% 2.35/0.71  fof(f50,plain,(
% 2.35/0.71    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.35/0.71    inference(ennf_transformation,[],[f4])).
% 2.35/0.71  fof(f4,axiom,(
% 2.35/0.71    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).
% 2.35/0.71  fof(f4948,plain,(
% 2.35/0.71    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))),
% 2.35/0.71    inference(forward_demodulation,[],[f4947,f313])).
% 2.35/0.71  fof(f4947,plain,(
% 2.35/0.71    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))),
% 2.35/0.71    inference(forward_demodulation,[],[f4946,f198])).
% 2.35/0.71  fof(f4946,plain,(
% 2.35/0.71    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))),
% 2.35/0.71    inference(forward_demodulation,[],[f4945,f308])).
% 2.35/0.71  fof(f4945,plain,(
% 2.35/0.71    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))),
% 2.35/0.71    inference(subsumption_resolution,[],[f4944,f373])).
% 2.35/0.71  fof(f4944,plain,(
% 2.35/0.71    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))),
% 2.35/0.71    inference(subsumption_resolution,[],[f4943,f367])).
% 2.35/0.71  fof(f4943,plain,(
% 2.35/0.71    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))),
% 2.35/0.71    inference(subsumption_resolution,[],[f4942,f361])).
% 2.35/0.71  fof(f4942,plain,(
% 2.35/0.71    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))),
% 2.35/0.71    inference(duplicate_literal_removal,[],[f4939])).
% 2.35/0.71  fof(f4939,plain,(
% 2.35/0.71    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))),
% 2.35/0.71    inference(superposition,[],[f738,f3025])).
% 2.35/0.71  fof(f3025,plain,(
% 2.35/0.71    u1_struct_0(sK1) = sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))),
% 2.35/0.71    inference(subsumption_resolution,[],[f3024,f367])).
% 2.35/0.71  fof(f3024,plain,(
% 2.35/0.71    ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | u1_struct_0(sK1) = sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))),
% 2.35/0.71    inference(subsumption_resolution,[],[f3017,f361])).
% 2.35/0.71  fof(f3017,plain,(
% 2.35/0.71    ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | u1_struct_0(sK1) = sK4(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))),
% 2.35/0.71    inference(resolution,[],[f746,f373])).
% 2.35/0.71  fof(f746,plain,(
% 2.35/0.71    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) | u1_struct_0(sK1) = sK4(sK0,sK1,X2) | k9_tmap_1(sK0,sK1) = X2) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f745,f62])).
% 2.35/0.71  fof(f745,plain,(
% 2.35/0.71    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | u1_struct_0(sK1) = sK4(sK0,sK1,X2) | k9_tmap_1(sK0,sK1) = X2) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f744,f61])).
% 2.35/0.71  fof(f744,plain,(
% 2.35/0.71    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | u1_struct_0(sK1) = sK4(sK0,sK1,X2) | k9_tmap_1(sK0,sK1) = X2) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f743,f64])).
% 2.35/0.71  fof(f743,plain,(
% 2.35/0.71    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | u1_struct_0(sK1) = sK4(sK0,sK1,X2) | k9_tmap_1(sK0,sK1) = X2) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f716,f63])).
% 2.35/0.71  fof(f716,plain,(
% 2.35/0.71    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | u1_struct_0(sK1) = sK4(sK0,sK1,X2) | k9_tmap_1(sK0,sK1) = X2) )),
% 2.35/0.71    inference(superposition,[],[f76,f313])).
% 2.35/0.71  fof(f76,plain,(
% 2.35/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | v2_struct_0(X0) | u1_struct_0(X1) = sK4(X0,X1,X2) | k9_tmap_1(X0,X1) = X2) )),
% 2.35/0.71    inference(cnf_transformation,[],[f31])).
% 2.35/0.71  fof(f31,plain,(
% 2.35/0.71    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.35/0.71    inference(flattening,[],[f30])).
% 2.35/0.71  fof(f30,plain,(
% 2.35/0.71    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.35/0.71    inference(ennf_transformation,[],[f7])).
% 2.35/0.71  fof(f7,axiom,(
% 2.35/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).
% 2.35/0.71  fof(f738,plain,(
% 2.35/0.71    ( ! [X0] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X0))),X0,k7_tmap_1(sK0,sK4(sK0,sK1,X0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = X0) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f737,f62])).
% 2.35/0.71  fof(f737,plain,(
% 2.35/0.71    ( ! [X0] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X0))),X0,k7_tmap_1(sK0,sK4(sK0,sK1,X0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | v2_struct_0(sK0) | k9_tmap_1(sK0,sK1) = X0) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f736,f61])).
% 2.35/0.71  fof(f736,plain,(
% 2.35/0.71    ( ! [X0] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X0))),X0,k7_tmap_1(sK0,sK4(sK0,sK1,X0))) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | v2_struct_0(sK0) | k9_tmap_1(sK0,sK1) = X0) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f735,f64])).
% 2.35/0.71  fof(f735,plain,(
% 2.35/0.71    ( ! [X0] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X0))),X0,k7_tmap_1(sK0,sK4(sK0,sK1,X0))) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | v2_struct_0(sK0) | k9_tmap_1(sK0,sK1) = X0) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f714,f63])).
% 2.35/0.71  fof(f714,plain,(
% 2.35/0.71    ( ! [X0] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,X0))),X0,k7_tmap_1(sK0,sK4(sK0,sK1,X0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | v2_struct_0(sK0) | k9_tmap_1(sK0,sK1) = X0) )),
% 2.35/0.71    inference(superposition,[],[f77,f313])).
% 2.35/0.71  fof(f77,plain,(
% 2.35/0.71    ( ! [X2,X0,X1] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | v2_struct_0(X0) | k9_tmap_1(X0,X1) = X2) )),
% 2.35/0.71    inference(cnf_transformation,[],[f31])).
% 2.35/0.71  fof(f58,plain,(
% 2.35/0.71    v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | v1_tsep_1(sK1,sK0)),
% 2.35/0.71    inference(cnf_transformation,[],[f21])).
% 2.35/0.71  fof(f5828,plain,(
% 2.35/0.71    ~v3_pre_topc(u1_struct_0(sK1),sK0) | v1_tsep_1(sK1,sK0)),
% 2.35/0.71    inference(subsumption_resolution,[],[f5827,f64])).
% 2.35/0.71  fof(f5827,plain,(
% 2.35/0.71    ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | v1_tsep_1(sK1,sK0)),
% 2.35/0.71    inference(subsumption_resolution,[],[f5826,f61])).
% 2.35/0.71  fof(f5826,plain,(
% 2.35/0.71    ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | v1_tsep_1(sK1,sK0)),
% 2.35/0.71    inference(superposition,[],[f71,f4984])).
% 2.35/0.71  fof(f4984,plain,(
% 2.35/0.71    u1_struct_0(sK1) = sK2(sK0,sK1)),
% 2.35/0.71    inference(subsumption_resolution,[],[f4983,f165])).
% 2.35/0.71  fof(f165,plain,(
% 2.35/0.71    v1_tsep_1(sK1,sK0) | u1_struct_0(sK1) = sK2(sK0,sK1)),
% 2.35/0.71    inference(subsumption_resolution,[],[f163,f64])).
% 2.35/0.71  fof(f163,plain,(
% 2.35/0.71    ~l1_pre_topc(sK0) | u1_struct_0(sK1) = sK2(sK0,sK1) | v1_tsep_1(sK1,sK0)),
% 2.35/0.71    inference(resolution,[],[f70,f61])).
% 2.35/0.71  fof(f70,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tsep_1(X1,X0)) )),
% 2.35/0.71    inference(cnf_transformation,[],[f26])).
% 2.35/0.71  fof(f26,plain,(
% 2.35/0.71    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.35/0.71    inference(flattening,[],[f25])).
% 2.35/0.71  fof(f25,plain,(
% 2.35/0.71    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.35/0.71    inference(ennf_transformation,[],[f8])).
% 2.35/0.71  fof(f8,axiom,(
% 2.35/0.71    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).
% 2.35/0.71  fof(f4983,plain,(
% 2.35/0.71    ~v1_tsep_1(sK1,sK0) | u1_struct_0(sK1) = sK2(sK0,sK1)),
% 2.35/0.71    inference(resolution,[],[f4953,f1033])).
% 2.35/0.71  fof(f1033,plain,(
% 2.35/0.71    v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1)) | u1_struct_0(sK1) = sK2(sK0,sK1)),
% 2.35/0.71    inference(resolution,[],[f339,f389])).
% 2.35/0.71  fof(f389,plain,(
% 2.35/0.71    v3_pre_topc(u1_struct_0(sK1),sK0) | u1_struct_0(sK1) = sK2(sK0,sK1)),
% 2.35/0.71    inference(subsumption_resolution,[],[f388,f64])).
% 2.35/0.71  fof(f388,plain,(
% 2.35/0.71    u1_struct_0(sK1) = sK2(sK0,sK1) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0)),
% 2.35/0.71    inference(subsumption_resolution,[],[f387,f61])).
% 2.35/0.71  fof(f387,plain,(
% 2.35/0.71    u1_struct_0(sK1) = sK2(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0)),
% 2.35/0.71    inference(resolution,[],[f165,f112])).
% 2.35/0.71  fof(f112,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0)) )),
% 2.35/0.71    inference(subsumption_resolution,[],[f106,f67])).
% 2.35/0.71  fof(f106,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0)) )),
% 2.35/0.71    inference(equality_resolution,[],[f68])).
% 2.35/0.71  fof(f68,plain,(
% 2.35/0.71    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0)) )),
% 2.35/0.71    inference(cnf_transformation,[],[f26])).
% 2.35/0.71  fof(f71,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~v3_pre_topc(sK2(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tsep_1(X1,X0)) )),
% 2.35/0.71    inference(cnf_transformation,[],[f26])).
% 2.35/0.71  fof(f4953,plain,(
% 2.35/0.71    ~v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1)) | ~v1_tsep_1(sK1,sK0)),
% 2.35/0.71    inference(backward_demodulation,[],[f225,f4949])).
% 2.35/0.71  fof(f225,plain,(
% 2.35/0.71    ~v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | ~v1_tsep_1(sK1,sK0)),
% 2.35/0.71    inference(subsumption_resolution,[],[f211,f224])).
% 2.35/0.71  fof(f224,plain,(
% 2.35/0.71    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))),
% 2.35/0.71    inference(subsumption_resolution,[],[f223,f62])).
% 2.35/0.71  fof(f223,plain,(
% 2.35/0.71    v2_struct_0(sK0) | m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))),
% 2.35/0.71    inference(subsumption_resolution,[],[f222,f64])).
% 2.35/0.71  fof(f222,plain,(
% 2.35/0.71    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))),
% 2.35/0.71    inference(subsumption_resolution,[],[f219,f63])).
% 2.35/0.71  fof(f219,plain,(
% 2.35/0.71    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))),
% 2.35/0.71    inference(resolution,[],[f92,f61])).
% 2.35/0.71  fof(f92,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f41])).
% 2.35/0.71  fof(f41,plain,(
% 2.35/0.71    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.35/0.71    inference(flattening,[],[f40])).
% 2.35/0.71  fof(f40,plain,(
% 2.35/0.71    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.35/0.71    inference(ennf_transformation,[],[f12])).
% 2.35/0.71  fof(f12,axiom,(
% 2.35/0.71    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).
% 2.35/0.71  fof(f211,plain,(
% 2.35/0.71    ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | ~v1_tsep_1(sK1,sK0)),
% 2.35/0.71    inference(subsumption_resolution,[],[f132,f210])).
% 2.35/0.71  fof(f210,plain,(
% 2.35/0.71    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))),
% 2.35/0.71    inference(subsumption_resolution,[],[f209,f62])).
% 2.35/0.71  fof(f209,plain,(
% 2.35/0.71    v2_struct_0(sK0) | v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))),
% 2.35/0.71    inference(subsumption_resolution,[],[f208,f64])).
% 2.35/0.71  fof(f208,plain,(
% 2.35/0.71    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))),
% 2.35/0.71    inference(subsumption_resolution,[],[f205,f63])).
% 2.35/0.71  fof(f205,plain,(
% 2.35/0.71    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))),
% 2.35/0.71    inference(resolution,[],[f91,f61])).
% 2.35/0.71  fof(f91,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f41])).
% 2.35/0.71  fof(f132,plain,(
% 2.35/0.71    ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_tsep_1(sK1,sK0)),
% 2.35/0.71    inference(subsumption_resolution,[],[f111,f131])).
% 2.35/0.71  fof(f131,plain,(
% 2.35/0.71    v1_funct_1(k9_tmap_1(sK0,sK1))),
% 2.35/0.71    inference(subsumption_resolution,[],[f130,f62])).
% 2.35/0.71  fof(f130,plain,(
% 2.35/0.71    v2_struct_0(sK0) | v1_funct_1(k9_tmap_1(sK0,sK1))),
% 2.35/0.71    inference(subsumption_resolution,[],[f129,f64])).
% 2.35/0.71  fof(f129,plain,(
% 2.35/0.71    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k9_tmap_1(sK0,sK1))),
% 2.35/0.71    inference(subsumption_resolution,[],[f128,f63])).
% 2.35/0.71  fof(f128,plain,(
% 2.35/0.71    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k9_tmap_1(sK0,sK1))),
% 2.35/0.71    inference(resolution,[],[f90,f61])).
% 2.35/0.71  fof(f90,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_1(k9_tmap_1(X0,X1))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f41])).
% 2.35/0.71  fof(f111,plain,(
% 2.35/0.71    ~v1_funct_1(k9_tmap_1(sK0,sK1)) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_tsep_1(sK1,sK0)),
% 2.35/0.71    inference(subsumption_resolution,[],[f60,f61])).
% 2.35/0.72  fof(f60,plain,(
% 2.35/0.72    ~v1_funct_1(k9_tmap_1(sK0,sK1)) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v5_pre_topc(k9_tmap_1(sK0,sK1),sK0,k8_tmap_1(sK0,sK1)) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0)),
% 2.35/0.72    inference(cnf_transformation,[],[f21])).
% 2.35/0.72  fof(f339,plain,(
% 2.35/0.72    ~v3_pre_topc(u1_struct_0(sK1),sK0) | v5_pre_topc(k6_partfun1(u1_struct_0(sK0)),sK0,k8_tmap_1(sK0,sK1))),
% 2.35/0.72    inference(forward_demodulation,[],[f338,f308])).
% 2.35/0.72  fof(f338,plain,(
% 2.35/0.72    v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k8_tmap_1(sK0,sK1)) | ~v3_pre_topc(u1_struct_0(sK1),sK0)),
% 2.35/0.72    inference(forward_demodulation,[],[f337,f198])).
% 2.35/0.72  fof(f337,plain,(
% 2.35/0.72    v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k6_tmap_1(sK0,u1_struct_0(sK1))) | ~v3_pre_topc(u1_struct_0(sK1),sK0)),
% 2.35/0.72    inference(subsumption_resolution,[],[f336,f62])).
% 2.35/0.72  fof(f336,plain,(
% 2.35/0.72    v2_struct_0(sK0) | v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k6_tmap_1(sK0,u1_struct_0(sK1))) | ~v3_pre_topc(u1_struct_0(sK1),sK0)),
% 2.35/0.72    inference(subsumption_resolution,[],[f335,f64])).
% 2.35/0.72  fof(f335,plain,(
% 2.35/0.72    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k6_tmap_1(sK0,u1_struct_0(sK1))) | ~v3_pre_topc(u1_struct_0(sK1),sK0)),
% 2.35/0.72    inference(subsumption_resolution,[],[f297,f63])).
% 2.35/0.72  fof(f297,plain,(
% 2.35/0.72    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v5_pre_topc(k7_tmap_1(sK0,u1_struct_0(sK1)),sK0,k6_tmap_1(sK0,u1_struct_0(sK1))) | ~v3_pre_topc(u1_struct_0(sK1),sK0)),
% 2.35/0.72    inference(resolution,[],[f127,f87])).
% 2.35/0.72  fof(f87,plain,(
% 2.35/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) )),
% 2.35/0.72    inference(cnf_transformation,[],[f39])).
% 2.35/0.72  fof(f5924,plain,(
% 2.35/0.72    v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0)),
% 2.35/0.72    inference(subsumption_resolution,[],[f5923,f61])).
% 2.35/0.72  fof(f5923,plain,(
% 2.35/0.72    ~m1_pre_topc(sK1,sK0) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0)),
% 2.35/0.72    inference(resolution,[],[f5829,f112])).
% 2.35/0.72  % SZS output end Proof for theBenchmark
% 2.35/0.72  % (31001)------------------------------
% 2.35/0.72  % (31001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.35/0.72  % (31001)Termination reason: Refutation
% 2.35/0.72  
% 2.35/0.72  % (31001)Memory used [KB]: 4733
% 2.35/0.72  % (31001)Time elapsed: 0.292 s
% 2.35/0.72  % (31001)------------------------------
% 2.35/0.72  % (31001)------------------------------
% 2.35/0.72  % (30983)Success in time 0.361 s
%------------------------------------------------------------------------------
